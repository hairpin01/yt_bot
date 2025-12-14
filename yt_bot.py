# -*- coding: utf-8 -*-
import os
import logging
import re
import json
from typing import Dict, List, Optional
from datetime import datetime, timedelta
import asyncio
import time
import traceback
import hashlib
import shutil
import random
import secrets
import string
import urllib.parse
import threading
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, InlineQueryResultArticle, InputTextMessageContent
from telegram.ext import (
    Application, CommandHandler, MessageHandler, CallbackQueryHandler,
    filters, ContextTypes, InlineQueryHandler, ConversationHandler
)
from telegram.error import NetworkError, RetryAfter, TimedOut, BadRequest
import yt_dlp

# Настройка логирования
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)

BOT_TOKEN = "BOT_TOKEN"
ADMIN_ID = "12345678"  # Ваш ID в Telegram

# Глобальные словари
inline_query_cache = {}
user_videos = {}
user_data = {}
user_searches = {}
download_queue = asyncio.Queue()
queue_status = {}
queue_processing = False  # Флаг обработки очереди
download_executor = ThreadPoolExecutor(max_workers=3)
USER_DATA_FILE = "user_data.json"


CACHE_FILE = "video_cache.json"
CACHE_DIR = "video_cache"

COOKIES_FILES = [
    "cookies.txt",
    "cookies.yaml",
    "cookies.json",
    os.path.expanduser("~/.config/youtube-dl/cookies.txt"),
]

SUBSCRIPTIONS_FILE = "subscriptions.json"
CHECK_INTERVAL = 3600
subscriptions = {}
subscription_tasks = {}


SUPPORTED_BROWSERS = ['chrome', 'firefox', 'edge', 'opera', 'vivaldi', 'safari']

SEARCH_QUERY, SEARCH_RESULT = range(2)

SEND_FILE_TIMEOUT = 300  # 5 минут
EDIT_MESSAGE_TIMEOUT = 30  # 30 секунд


if not os.path.exists(CACHE_DIR):
    os.makedirs(CACHE_DIR)

def generate_cache_key():
    """Генерирует случайный ключ для кэша"""
    alphabet = string.ascii_letters + string.digits
    return ''.join(secrets.choice(alphabet) for _ in range(16))

def cache_inline_query(url, action_type):
    """Сохраняет URL в кэш и возвращает ключ"""
    cache_key = generate_cache_key()
    inline_query_cache[cache_key] = {
        'url': url,
        'action_type': action_type,
        'timestamp': time.time()
    }
    return cache_key

def get_cached_query(cache_key):
    """Получает URL из кэша по ключу"""
    if cache_key in inline_query_cache:
        return inline_query_cache[cache_key]
    return None


def clean_old_cache():
    """Очищает записи кэша старше 1 часа"""
    current_time = time.time()
    keys_to_remove = []
    for key, data in inline_query_cache.items():
        if current_time - data['timestamp'] > 3600:  # 1 час
            keys_to_remove.append(key)
    for key in keys_to_remove:
        del inline_query_cache[key]


def normalize_url(url):
    """
    Приводит URL к единому формату для сравнения.
    Убирает лишние параметры, приводит к стандартному виду.
    """
    try:
        # Парсим URL
        parsed = urllib.parse.urlparse(url)

        # Нормализуем домен
        domain = parsed.netloc.lower()

        # Обрабатываем короткие ссылки youtu.be
        if domain == 'youtu.be':
            # Извлекаем ID видео из пути
            video_id = parsed.path.lstrip('/').split('/')[0]  # Берем первую часть пути
            # Убираем возможные параметры в пути
            video_id = video_id.split('?')[0]
            return f"https://www.youtube.com/watch?v={video_id}"

        # Обрабатываем стандартные ссылки YouTube
        elif 'youtube.com' in domain or 'youtube.com' in domain:
            # Стандартизируем домен YouTube
            domain = 'www.youtube.com'

            # Обрабатываем параметры запроса
            query_params = urllib.parse.parse_qs(parsed.query)

            # Для YouTube оставляем только параметр v (video ID)
            if 'v' in query_params:
                video_id = query_params['v'][0]
                # Убираем все остальные параметры
                return f"https://{domain}/watch?v={video_id}"

        # Для TikTok пытаемся извлечь ID видео
        if 'tiktok.com' in domain:
            # Пытаемся найти ID видео в пути
            path_parts = parsed.path.split('/')
            if 'video' in path_parts and len(path_parts) > path_parts.index('video') + 1:
                video_id = path_parts[path_parts.index('video') + 1]
                return f"https://www.tiktok.com/@user/video/{video_id}"

        # Для других URL просто возвращаем нормализованную версию
        return f"{parsed.scheme}://{domain}{parsed.path}"

    except Exception as e:
        logger.error(f"Ошибка при нормализации URL {url}: {e}")
        return url

# Загрузка данных пользователей из файла
def load_user_data():
    global user_data
    try:
        if os.path.exists(USER_DATA_FILE):
            with open(USER_DATA_FILE, 'r', encoding='utf-8') as f:
                user_data = json.load(f)
                logger.info(f"Загружены данные {len(user_data)} пользователей")
    except Exception as e:
        logger.error(f"Ошибка при загрузке данных пользователей: {e}")
        logger.error(traceback.format_exc())

# Сохранение данных пользователей в файл
def save_user_data():
    try:
        with open(USER_DATA_FILE, 'w', encoding='utf-8') as f:
            json.dump(user_data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"Ошибка при сохранении данных пользователей: {e}")
        logger.error(traceback.format_exc())

# Загрузка кэша видео из файла
def load_video_cache():
    video_cache = {}
    try:
        if os.path.exists(CACHE_FILE):
            with open(CACHE_FILE, 'r', encoding='utf-8') as f:
                video_cache = json.load(f)
                logger.info(f"Загружено {len(video_cache)} видео в кэше")
    except Exception as e:
        logger.error(f"Ошибка при загрузке кэша видео: {e}")
        logger.error(traceback.format_exc())
    return video_cache

# Сохранение кэша видео в файл
def save_video_cache(video_cache):
    try:
        with open(CACHE_FILE, 'w', encoding='utf-8') as f:
            json.dump(video_cache, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"Ошибка при сохранении кэша видео: {e}")
        logger.error(traceback.format_exc())

# Генерация хэша для URL
def get_url_hash(url):
    # Нормализуем URL перед хэшированием
    normalized_url = normalize_url(url)
    return hashlib.md5(normalized_url.encode('utf-8')).hexdigest()

# Проверка наличия видео в кэше
def check_video_cache(url, video_cache):
    url_hash = get_url_hash(url)
    if url_hash in video_cache:
        cache_entry = video_cache[url_hash]
        # Проверяем, существует ли файл
        if os.path.exists(cache_entry['file_path']):
            return cache_entry
    return None

# Получение информации о кэшированных версиях видео
def get_cached_versions(url):
    video_cache = load_video_cache()
    cached_versions = []

    # Нормализуем URL для поиска
    normalized_url = normalize_url(url)
    logger.info(f"Поиск в кэше для URL: {url} (нормализованный: {normalized_url})")

    for url_hash, cache_data in video_cache.items():
        # Нормализуем URL из кэша для сравнения
        cached_normalized_url = normalize_url(cache_data['url'])
        logger.info(f"Кэш запись: {cache_data['url']} (нормализованный: {cached_normalized_url})")

        if cached_normalized_url == normalized_url and os.path.exists(cache_data['file_path']):
            cached_versions.append(cache_data)

    logger.info(f"Найдено {len(cached_versions)} кэшированных версий для URL: {url}")
    return cached_versions

# Добавление видео в кэш
def add_to_video_cache(url, file_path, format_id, quality, duration, title, url_type):
    try:
        video_cache = load_video_cache()
        url_hash = get_url_hash(url)

        # Перемещаем файл в кэш-директорию
        filename = os.path.basename(file_path)
        cache_file_path = os.path.join(CACHE_DIR, filename)

        # Если файл уже не в кэш-директории, перемещаем его
        if os.path.dirname(file_path) != CACHE_DIR:
            shutil.move(file_path, cache_file_path)
        else:
            cache_file_path = file_path

        # Добавляем запись в кэш
        video_cache[url_hash] = {
            'url': url,  # Сохраняем оригинальный URL
            'file_path': cache_file_path,
            'format_id': format_id,
            'quality': quality,
            'duration': duration,
            'title': title,
            'url_type': url_type,
            'cached_date': time.time(),
            'normalized_url': normalize_url(url)  # Добавляем нормализованный URL для поиска
        }

        save_video_cache(video_cache)
        logger.info(f"Видео добавлено в кэш: {url} (нормализованный: {normalize_url(url)})")
        return cache_file_path
    except Exception as e:
        logger.error(f"Ошибка при добавлении видео в кэш: {e}")
        logger.error(traceback.format_exc())
        return file_path

def get_url_type(url):
    """Определяет тип URL (youtube, youtube_music, tiktok, unknown)"""
    try:
        # Приводим URL к нижнему регистру для упрощения проверки
        url_lower = url.lower()

        # Убираем возможные пробелы в начале и конце
        url_lower = url_lower.strip()

        # Проверяем YouTube (включая короткие ссылки youtu.be)
        if any(domain in url_lower for domain in ['youtube.com', 'youtu.be']):
            # Проверяем YouTube Music отдельно
            if 'music.youtube.com' in url_lower:
                return 'youtube_music'
            else:
                return 'youtube'

        # Проверяем TikTok
        elif any(domain in url_lower for domain in ['tiktok.com', 'vt.tiktok.com', 'vm.tiktok.com']):
            return 'tiktok'

        else:
            logger.info(f"Неизвестный тип URL: {url_lower}")
            return 'unknown'

    except Exception as e:
        logger.error(f"Ошибка при определении типа URL {url}: {e}")
        return 'unknown'

def get_video_info(url, url_type):
    """Получает информацию о видео с помощью yt-dlp"""
    ydl_opts = {
        'quiet': True,
        'no_warnings': True,
        'extract_flat': False,
        # Добавляем параметры для работы с SSL
        'no_check_certificate': True,
        'socket_timeout': 30,
        'source_address': '0.0.0.0',
    }

    # Добавляем cookies для YouTube, если доступны
    if url_type in ['youtube', 'youtube_music']:
        for cookies_file in COOKIES_FILES:
            if os.path.exists(cookies_file):
                ydl_opts['cookiefile'] = cookies_file
                logger.info(f"Используем cookies файл: {cookies_file}")
                break

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            return info
    except Exception as e:
        logger.error(f"Ошибка при получении информации о видео: {e}")
        logger.error(traceback.format_exc())
        raise e

# Создание клавиатуры с выбором качества
def create_quality_keyboard(formats, url, user_id, url_type, is_inline=False):
    keyboard = []

    # Фильтруем форматы видео
    video_formats = []
    for f in formats:
        if f.get('vcodec') != 'none' and f.get('acodec') != 'none':  # И видео, и аудио
            if f.get('height'):  # Проверяем наличие высоты (качества видео)
                video_formats.append(f)

    # Сортируем видео форматы по качеству (от высшего к низшему)
    video_formats.sort(key=lambda x: x.get('height', 0), reverse=True)

    # Добавляем кнопки для видео форматов
    for i, fmt in enumerate(video_formats[:5]):  # Ограничиваем до 5 вариантов
        height = fmt.get('height', 'Unknown')
        fps = fmt.get('fps', 0)
        format_note = fmt.get('format_note', '')
        filesize = fmt.get('filesize', fmt.get('filesize_approx', 0))

        # Форматируем текст кнопки
        quality_text = f"{height}p"
        if fps and fps > 30:
            quality_text += f" ({fps}fps)"
        if format_note and format_note != height:
            quality_text += f" {format_note}"
        if filesize:
            size_mb = filesize // 1024 // 1024
            quality_text += f" ({size_mb}MB)"

        callback_data = f"video:{fmt['format_id']}:{user_id}"
        if is_inline:
            callback_data += ":inline"

        keyboard.append([InlineKeyboardButton(f"🎥 {quality_text}", callback_data=callback_data)])

    # Добавляем кнопку для лучшего качества (до 1080p)
    callback_data = f"best:{user_id}"
    if is_inline:
        callback_data += ":inline"
    keyboard.append([InlineKeyboardButton("✨ Лучшее качество до 1080p", callback_data=callback_data)])

    # Добавляем кнопку для максимального качества (есть варианты выше 1080p)
    has_high_quality = any(f.get('height', 0) > 1080 for f in video_formats)
    if has_high_quality:
        callback_data = f"max:{user_id}"
        if is_inline:
            callback_data += ":inline"
        keyboard.append([InlineKeyboardButton("🔥 Максимальное качество", callback_data=callback_data)])

    # Добавляем кнопку для только аудио (только для YouTube и YouTube Music)
    if url_type in ['youtube', 'youtube_music']:
        callback_data = f"audio:{user_id}"
        if is_inline:
            callback_data += ":inline"
        keyboard.append([InlineKeyboardButton("🎵 Только аудио", callback_data=callback_data)])

    return InlineKeyboardMarkup(keyboard)

# Создание клавиатуры с выбором: использовать кэш или скачать заново
def create_cache_choice_keyboard(url, user_id, cached_versions, is_inline=False):
    keyboard = []

    # Добавляем кнопки для каждой кэшированной версии
    for i, cache_data in enumerate(cached_versions):
        quality = cache_data.get('quality', 'Unknown')
        # Безопасная проверка format_id
        format_id = cache_data.get('format_id', '')
        if format_id and isinstance(format_id, str) and format_id.startswith('video'):
            format_type = 'video'
        else:
            format_type = 'audio'
        size_text = ""

        # Получаем размер файла
        if os.path.exists(cache_data['file_path']):
            file_size = os.path.getsize(cache_data['file_path'])
            size_text = f" ({file_size//1024//1024}MB)"

        callback_data = f"cache:{i}:{user_id}"
        if is_inline:
            callback_data += ":inline"

        keyboard.append([InlineKeyboardButton(
            f"📦 Использовать кэш: {quality} ({format_type}){size_text}",
            callback_data=callback_data
        )])

    # Добавляем кнопку для скачивания нового
    callback_data = f"new_download:{user_id}"
    if is_inline:
        callback_data += ":inline"

    keyboard.append([InlineKeyboardButton(
        "🔄 Скачать новое видео (выбрать качество)",
        callback_data=callback_data
    )])

    return InlineKeyboardMarkup(keyboard)

def download_video_sync(url, format_type, format_id=None, url_type='youtube', progress_hook=None):
    """Синхронная функция скачивания видео с поддержкой прогресса"""
    # Добавляем случайную задержку для избежания блокировок
    time.sleep(random.uniform(1, 3))

    ydl_opts = {
        'quiet': True,
        'no_warnings': True,
        'outtmpl': '%(title)s.%(ext)s',
        'no_check_certificate': True,
        'socket_timeout': 30,
        'source_address': '0.0.0.0',
    }

    # Добавляем хук прогресса, если передан
    if progress_hook:
        ydl_opts['progress_hooks'] = [progress_hook]

    # Добавляем cookies для YouTube, если доступны
    if url_type in ['youtube', 'youtube_music']:
        for cookies_file in COOKIES_FILES:
            if os.path.exists(cookies_file):
                ydl_opts['cookiefile'] = cookies_file
                break

    # Настраиваем формат для скачивания
    if format_type == 'best':
        ydl_opts['format'] = 'best[height<=1080]'
    elif format_type == 'max':
        ydl_opts['format'] = 'best'
    elif format_type == 'audio':
        ydl_opts['format'] = 'bestaudio/best'
        ydl_opts['postprocessors'] = [{
            'key': 'FFmpegExtractAudio',
            'preferredcodec': 'mp3',
            'preferredquality': '192',
        }]
    elif format_id:
        ydl_opts['format'] = format_id

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=True)
            title = info.get('title', 'video')
            filename = ydl.prepare_filename(info)

            # Для аудио меняем расширение на mp3
            if format_type == 'audio' and not filename.endswith('.mp3'):
                base_name = os.path.splitext(filename)[0]
                filename = base_name + '.mp3'

            return filename, title
    except Exception as e:
        logger.error(f"Ошибка при скачивании видео: {e}")
        # Удаляем частично скачанный файл
        if 'filename' in locals():
            try:
                if os.path.exists(filename):
                    os.remove(filename)
            except:
                pass
        raise e

def download_audio_sync(url, url_type, progress_hook=None):
    """Синхронная функция скачивания аудио с поддержкой прогресса"""
    # Добавляем случайную задержку для избежания блокировок
    time.sleep(random.uniform(1, 3))

    ydl_opts = {
        'quiet': True,
        'no_warnings': True,
        'format': 'bestaudio/best',
        'outtmpl': '%(title)s.%(ext)s',
        'postprocessors': [{
            'key': 'FFmpegExtractAudio',
            'preferredcodec': 'mp3',
            'preferredquality': '192',
        }],
        'no_check_certificate': True,
        'socket_timeout': 30,
        'source_address': '0.0.0.0',
    }

    # Добавляем хук прогресса, если передан
    if progress_hook:
        ydl_opts['progress_hooks'] = [progress_hook]

    # Добавляем cookies для YouTube, если доступны
    if url_type in ['youtube', 'youtube_music']:
        for cookies_file in COOKIES_FILES:
            if os.path.exists(cookies_file):
                ydl_opts['cookiefile'] = cookies_file
                break

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=True)
            title = info.get('title', 'audio')
            filename = ydl.prepare_filename(info)

            # Меняем расширение на mp3
            base_name = os.path.splitext(filename)[0]
            filename = base_name + '.mp3'

            return filename, title
    except Exception as e:
        logger.error(f"Ошибка при скачивании аудио: {e}")
        # Удаляем частично скачанный файл
        if 'filename' in locals():
            try:
                if os.path.exists(filename):
                    os.remove(filename)
            except:
                pass
        raise e

def load_subscriptions():
    """Загружает подписки из файла"""
    global subscriptions
    try:
        if os.path.exists(SUBSCRIPTIONS_FILE):
            with open(SUBSCRIPTIONS_FILE, 'r', encoding='utf-8') as f:
                subscriptions = json.load(f)
            logger.info(f"Загружено {len(subscriptions)} подписок")
    except Exception as e:
        logger.error(f"Ошибка при загрузке подписок: {e}")
        subscriptions = {}

def save_subscriptions():
    """Сохраняет подписки в файл"""
    try:
        with open(SUBSCRIPTIONS_FILE, 'w', encoding='utf-8') as f:
            json.dump(subscriptions, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"Ошибка при сохранении подписок: {e}")

def get_channel_info(url):
    """Получает информацию о канале"""
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'extract_flat': True,
            'skip_download': True,
        }

        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)

            # Получаем ID канала
            channel_id = info.get('channel_id')
            if not channel_id and 'uploader_id' in info:
                channel_id = info['uploader_id']

            return {
                'channel_id': channel_id,
                'title': info.get('uploader', 'Неизвестный канал'),
                'url': info.get('webpage_url', url),
                'description': info.get('description', ''),
                'subscriber_count': info.get('subscriber_count', 0)
            }
    except Exception as e:
        logger.error(f"Ошибка при получении информации о канале: {e}")
        return None

def get_latest_videos(channel_url, max_results=5):
    """Получает последние видео с канала"""
    try:
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'extract_flat': True,
            'skip_download': True,
            'playlistend': max_results,
        }

        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(channel_url, download=False)

            videos = []
            if 'entries' in info:
                for entry in info['entries']:
                    if entry:
                        videos.append({
                            'id': entry.get('id'),
                            'title': entry.get('title'),
                            'url': entry.get('url'),
                            'upload_date': entry.get('upload_date'),
                            'duration': entry.get('duration'),
                            'view_count': entry.get('view_count')
                        })

            return videos
    except Exception as e:
        logger.error(f"Ошибка при получении видео с канала: {e}")
        return []

async def subscribe_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Подписаться на канал"""
    try:
        user = update.effective_user
        user_id = str(user.id)

        if not context.args:
            await update.message.reply_text(
                "📝 Использование: /subscribe <ссылка на канал>\n\n"
                "Примеры:\n"
                "• /subscribe https://www.youtube.com/c/ChannelName\n"
                "• /subscribe https://www.youtube.com/@username\n"
                "• /subscribe https://www.youtube.com/channel/UC...\n\n"
                "💡 Бот будет присылать уведомления о новых видео."
            )
            return

        url = " ".join(context.args)

        # Проверяем, что это ссылка на канал
        if 'youtube.com' not in url or ('/c/' not in url and '/@' not in url and '/channel/' not in url):
            await update.message.reply_text(
                "❌ Это не похоже на ссылку на YouTube канал.\n\n"
                "Поддерживаются ссылки на каналы в форматах:\n"
                "• https://www.youtube.com/c/ChannelName\n"
                "• https://www.youtube.com/@username\n"
                "• https://www.youtube.com/channel/UC..."
            )
            return

        msg = await update.message.reply_text("⏳ Получаю информацию о канале...")

        # Получаем информацию о канале
        channel_info = get_channel_info(url)
        if not channel_info:
            await msg.edit_text("❌ Не удалось получить информацию о канале.")
            return

        # Инициализируем подписки для пользователя, если их нет
        if user_id not in subscriptions:
            subscriptions[user_id] = {}

        # Проверяем, не подписан ли уже пользователь
        for sub in subscriptions[user_id].values():
            if sub.get('channel_id') == channel_info['channel_id']:
                await msg.edit_text(f"✅ Вы уже подписаны на канал: {channel_info['title']}")
                return

        # Получаем последние видео
        latest_videos = get_latest_videos(url, 3)

        # Добавляем подписку
        subscription_id = f"sub_{int(time.time())}_{user_id}"
        subscriptions[user_id][subscription_id] = {
            'channel_id': channel_info['channel_id'],
            'title': channel_info['title'],
            'url': channel_info['url'],
            'subscription_date': time.time(),
            'last_check': time.time(),
            'last_video_id': latest_videos[0]['id'] if latest_videos else None,
            'notifications_enabled': True
        }

        save_subscriptions()

        await msg.edit_text(
            f"✅ Вы успешно подписались на канал!\n\n"
            f"📺 Канал: {channel_info['title']}\n"
            f"👥 Подписчиков: {channel_info['subscriber_count']:,}\n"
            f"📅 Бот будет проверять новые видео каждый час.\n\n"
            f"🔔 Вы будете получать уведомления о новых видео в этом чате."
        )

        # Запускаем задачу проверки, если она еще не запущена
        if user_id not in subscription_tasks:
            asyncio.create_task(check_subscriptions_for_user(user_id, context.application))

    except Exception as e:
        logger.error(f"Ошибка в команде subscribe: {e}")
        await update.message.reply_text("❌ Произошла ошибка. Попробуйте позже.")

async def unsubscribe_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Отписаться от канала"""
    try:
        user = update.effective_user
        user_id = str(user.id)

        if user_id not in subscriptions or not subscriptions[user_id]:
            await update.message.reply_text("❌ У вас нет активных подписок.")
            return

        if not context.args:
            # Показываем список подписок для выбора
            keyboard = []
            for sub_id, sub_data in subscriptions[user_id].items():
                keyboard.append([InlineKeyboardButton(
                    f"❌ {sub_data['title']}",
                    callback_data=f"unsubscribe:{sub_id}:{user_id}"
                )])

            keyboard.append([InlineKeyboardButton("❌ Отписаться от всех", callback_data=f"unsubscribe_all:{user_id}")])

            await update.message.reply_text(
                "📋 Ваши подписки:\n\nВыберите канал для отписки:",
                reply_markup=InlineKeyboardMarkup(keyboard)
            )
            return

        # Отписаться по ID подписки
        sub_id = context.args[0]
        if sub_id in subscriptions[user_id]:
            channel_title = subscriptions[user_id][sub_id]['title']
            del subscriptions[user_id][sub_id]

            # Если подписок не осталось, удаляем пользователя из списка
            if not subscriptions[user_id]:
                del subscriptions[user_id]

            save_subscriptions()
            await update.message.reply_text(f"✅ Вы отписались от канала: {channel_title}")
        else:
            await update.message.reply_text("❌ Подписка не найдена.")

    except Exception as e:
        logger.error(f"Ошибка в команде unsubscribe: {e}")
        await update.message.reply_text("❌ Произошла ошибка. Попробуйте позже.")

async def list_subscriptions_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Показать список подписок"""
    try:
        user = update.effective_user
        user_id = str(user.id)

        if user_id not in subscriptions or not subscriptions[user_id]:
            await update.message.reply_text("📭 У вас пока нет подписок.\n\nИспользуйте /subscribe для подписки на каналы.")
            return

        message_text = "📋 Ваши подписки:\n\n"
        for sub_id, sub_data in subscriptions[user_id].items():
            days_subscribed = (time.time() - sub_data['subscription_date']) / 86400
            message_text += f"📺 {sub_data['title']}\n"
            message_text += f"   └─ Подписаны: {int(days_subscribed)} дней\n"
            message_text += f"   └─ Уведомления: {'🔔 Вкл' if sub_data['notifications_enabled'] else '🔕 Выкл'}\n\n"

        keyboard = [
            [InlineKeyboardButton("⚙️ Управление подписками", callback_data=f"manage_subs:{user_id}")],
            [InlineKeyboardButton("➕ Подписаться на канал", switch_inline_query_current_chat="/subscribe ")]
        ]

        await update.message.reply_text(
            message_text,
            reply_markup=InlineKeyboardMarkup(keyboard),
            disable_web_page_preview=True
        )

    except Exception as e:
        logger.error(f"Ошибка в команде subscriptions: {e}")
        await update.message.reply_text("❌ Произошла ошибка. Попробуйте позже.")

async def toggle_notifications_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Включить/выключить уведомления"""
    try:
        user = update.effective_user
        user_id = str(user.id)

        if user_id not in subscriptions or not subscriptions[user_id]:
            await update.message.reply_text("❌ У вас нет активных подписок.")
            return

        if not context.args:
            # Показываем список подписок для управления
            keyboard = []
            for sub_id, sub_data in subscriptions[user_id].items():
                status = "🔔" if sub_data['notifications_enabled'] else "🔕"
                keyboard.append([InlineKeyboardButton(
                    f"{status} {sub_data['title']}",
                    callback_data=f"toggle_notif:{sub_id}:{user_id}"
                )])

            await update.message.reply_text(
                "🔔 Управление уведомлениями:\n\nВыберите канал:",
                reply_markup=InlineKeyboardMarkup(keyboard)
            )
            return

    except Exception as e:
        logger.error(f"Ошибка в команде notifications: {e}")
        await update.message.reply_text("❌ Произошла ошибка. Попробуйте позже.")

async def check_subscriptions_for_user(user_id, app):
    """Проверяет новые видео для подписок пользователя"""
    while True:
        try:
            if user_id not in subscriptions or not subscriptions[user_id]:
                logger.info(f"Пользователь {user_id} не имеет подписок, останавливаем проверку")
                if user_id in subscription_tasks:
                    del subscription_tasks[user_id]
                break

            for sub_id, sub_data in list(subscriptions[user_id].items()):

                if not sub_data.get('notifications_enabled', True):
                    continue


                current_time = time.time()
                if current_time - sub_data['last_check'] < CHECK_INTERVAL:
                    continue


                subscriptions[user_id][sub_id]['last_check'] = current_time


                try:
                    latest_videos = get_latest_videos(sub_data['url'], 5)

                    if latest_videos:

                        last_known_video_id = sub_data.get('last_video_id')
                        new_videos = []

                        for video in latest_videos:
                            if video['id'] == last_known_video_id:
                                break
                            new_videos.append(video)

                        # Отправляем уведомления о новых видео
                        if new_videos:
                            for video in reversed(new_videos):  # От старых к новым
                                message_text = (
                                    f"🎬 Новое видео на канале {sub_data['title']}!\n\n"
                                    f"📹 {video['title']}\n"
                                    f"⏱ Длительность: {video['duration']} сек\n"
                                    f"👁 Просмотров: {video.get('view_count', 'N/A')}\n\n"
                                    f"🔗 Ссылка: {video['url']}"
                                )

                                keyboard = [
                                    [InlineKeyboardButton("📥 Скачать видео", callback_data=f"subscribe_dl:{video['url']}:{user_id}")],
                                    [InlineKeyboardButton("🔕 Отключить уведомления", callback_data=f"unsubscribe:{sub_id}:{user_id}")]
                                ]

                                try:
                                    await app.bot.send_message(
                                        chat_id=int(user_id),
                                        text=message_text,
                                        reply_markup=InlineKeyboardMarkup(keyboard),
                                        disable_web_page_preview=True
                                    )


                                    await asyncio.sleep(1)

                                except Exception as e:
                                    logger.error(f"Ошибка при отправке уведомления: {e}")


                            subscriptions[user_id][sub_id]['last_video_id'] = new_videos[0]['id']
                            save_subscriptions()

                except Exception as e:
                    logger.error(f"Ошибка при проверке канала {sub_data['title']}: {e}")


            save_subscriptions()

            await asyncio.sleep(CHECK_INTERVAL)

        except Exception as e:
            logger.error(f"Ошибка в задаче проверки подписок для пользователя {user_id}: {e}")
            await asyncio.sleep(300)

async def handle_subscription_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик callback-кнопок для подписок"""
    try:
        query = update.callback_query
        await query.answer()

        data = query.data
        parts = data.split(":")
        action = parts[0]

        if action == "unsubscribe":
            if len(parts) < 3:
                await query.edit_message_text("❌ Ошибка в данных запроса.")
                return

            sub_id = parts[1]
            user_id = parts[2]

            if user_id in subscriptions and sub_id in subscriptions[user_id]:
                channel_title = subscriptions[user_id][sub_id]['title']
                del subscriptions[user_id][sub_id]

                if not subscriptions[user_id]:
                    del subscriptions[user_id]

                save_subscriptions()
                await query.edit_message_text(f"✅ Вы отписались от канала: {channel_title}")
            else:
                await query.edit_message_text("❌ Подписка не найдена.")

        elif action == "unsubscribe_all":
            user_id = parts[1]
            if user_id in subscriptions:
                del subscriptions[user_id]
                save_subscriptions()
                await query.edit_message_text("✅ Вы отписались от всех каналов.")
            else:
                await query.edit_message_text("❌ У вас нет активных подписок.")

        elif action == "toggle_notif":
            if len(parts) < 3:
                await query.edit_message_text("❌ Ошибка в данных запроса.")
                return

            sub_id = parts[1]
            user_id = parts[2]

            if user_id in subscriptions and sub_id in subscriptions[user_id]:
                current_status = subscriptions[user_id][sub_id]['notifications_enabled']
                subscriptions[user_id][sub_id]['notifications_enabled'] = not current_status
                save_subscriptions()

                status_text = "включены" if not current_status else "отключены"
                await query.edit_message_text(f"✅ Уведомления для канала {subscriptions[user_id][sub_id]['title']} {status_text}.")
            else:
                await query.edit_message_text("❌ Подписка не найдена.")

        elif action == "manage_subs":
            user_id = parts[1]
            # Показываем меню управления
            keyboard = []
            if user_id in subscriptions:
                for sub_id, sub_data in subscriptions[user_id].items():
                    keyboard.append([InlineKeyboardButton(
                        f"❌ {sub_data['title']}",
                        callback_data=f"unsubscribe:{sub_id}:{user_id}"
                    )])

            keyboard.append([InlineKeyboardButton("🔔 Управление уведомлениями", callback_data=f"toggle_menu:{user_id}")])
            keyboard.append([InlineKeyboardButton("➕ Добавить подписку", switch_inline_query_current_chat="/subscribe ")])

            await query.edit_message_text(
                "⚙️ Управление подписками:\n\nВыберите действие:",
                reply_markup=InlineKeyboardMarkup(keyboard)
            )

        elif action == "toggle_menu":
            user_id = parts[1]
            # Меню включения/выключения уведомлений
            keyboard = []
            if user_id in subscriptions:
                for sub_id, sub_data in subscriptions[user_id].items():
                    status = "🔔" if sub_data['notifications_enabled'] else "🔕"
                    keyboard.append([InlineKeyboardButton(
                        f"{status} {sub_data['title']}",
                        callback_data=f"toggle_notif:{sub_id}:{user_id}"
                    )])

            await query.edit_message_text(
                "🔔 Выберите канал для изменения настроек уведомлений:",
                reply_markup=InlineKeyboardMarkup(keyboard)
            )

        elif action == "subscribe_dl":
            # Скачать видео из уведомления
            if len(parts) < 3:
                await query.edit_message_text("❌ Ошибка в данных запроса.")
                return

            url = parts[1]
            user_id = int(parts[2])

            # Добавляем в очередь загрузки
            url_type = get_url_type(url)
            task = (user_id, url, "best", None, url_type, query.message, False)
            await download_queue.put(task)

            update_queue_positions()
            position = queue_status.get(user_id, 0)

            if position > 0:
                await query.edit_message_text(f"📋 Запрос на скачивание добавлен в очередь. Позиция: {position}")
            else:
                await query.edit_message_text("📋 Запрос на скачивание добавлен в очередь.")

            if not queue_processing:
                asyncio.create_task(process_download_queue(context.application))

    except Exception as e:
        logger.error(f"Ошибка в обработке подписок callback: {e}")




async def download_video_async(url, format_type, format_id=None, url_type='youtube', message=None):
    """Асинхронная обертка для скачивания видео с прогрессом"""
    loop = asyncio.get_event_loop()


    progress_hook = None
    if message:
        progress = DownloadProgress(message)
        progress.set_loop(loop)
        progress_hook = progress.progress_hook

    try:
        result = await loop.run_in_executor(
            download_executor,
            download_video_sync,
            url, format_type, format_id, url_type, progress_hook
        )
        return result
    except Exception as e:
        if "File size exceeded" in str(e):
            raise Exception("Файл слишком большой для Telegram (превышает 50 МБ)")
        logger.error(f"Ошибка в асинхронном скачивании: {e}")
        raise e

async def download_audio_async(url, url_type, message=None):
    """Асинхронная обертка для скачивания аудио с прогрессом"""
    loop = asyncio.get_event_loop()

    progress_hook = None
    if message:
        progress = DownloadProgress(message)
        progress.set_loop(loop)
        progress_hook = progress.progress_hook

    try:
        result = await loop.run_in_executor(
            download_executor,
            download_audio_sync,
            url, url_type, progress_hook
        )
        return result
    except Exception as e:
        if "File size exceeded" in str(e):
            raise Exception("Файл слишком большой для Telegram (превышает 50 МБ)")
        logger.error(f"Ошибка в асинхронном скачивании аудио: {e}")
        raise e

# Скачивание видео
def download_video(url, format_type, format_id=None, url_type='youtube'):
    """Скачивает видео по URL с выбранным качеством"""
    # Добавляем случайную задержку для избежания блокировок
    time.sleep(random.uniform(1, 3))

    ydl_opts = {
        'quiet': True,
        'no_warnings': True,
        'outtmpl': '%(title)s.%(ext)s',
        # Добавляем параметры для работы с SSL
        'no_check_certificate': True,
        'socket_timeout': 30,
        'source_address': '0.0.0.0',
    }

    # Добавляем cookies для YouTube, если доступны
    if url_type in ['youtube', 'youtube_music']:
        for cookies_file in COOKIES_FILES:
            if os.path.exists(cookies_file):
                ydl_opts['cookiefile'] = cookies_file
                break

    # Настраиваем формат для скачивания
    if format_type == 'best':
        ydl_opts['format'] = 'best[height<=1080]'  # Лучшее качество до 1080p
    elif format_type == 'max':
        ydl_opts['format'] = 'best'  # Абсолютно лучшее качество без ограничений
    elif format_type == 'audio':
        ydl_opts['format'] = 'bestaudio/best'
        ydl_opts['postprocessors'] = [{
            'key': 'FFmpegExtractAudio',
            'preferredcodec': 'mp3',
            'preferredquality': '192',
        }]
    elif format_id:
        ydl_opts['format'] = format_id

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=True)
            title = info.get('title', 'video')
            filename = ydl.prepare_filename(info)

            # Для аудио меняем расширение на mp3
            if format_type == 'audio' and not filename.endswith('.mp3'):
                base_name = os.path.splitext(filename)[0]
                filename = base_name + '.mp3'

            return filename, title
    except Exception as e:
        logger.error(f"Ошибка при скачивании видео: {e}")
        raise e

# Скачивание только аудио
def download_audio(url, url_type):
    """Скачивает только аудио из видео"""
    # Добавляем случайную задержку для избежания блокировок
    time.sleep(random.uniform(1, 3))

    ydl_opts = {
        'quiet': True,
        'no_warnings': True,
        'format': 'bestaudio/best',
        'outtmpl': '%(title)s.%(ext)s',
        'postprocessors': [{
            'key': 'FFmpegExtractAudio',
            'preferredcodec': 'mp3',
            'preferredquality': '192',
        }],
        # Добавляем параметры для работы с SSL
        'no_check_certificate': True,
        'socket_timeout': 30,
        'source_address': '0.0.0.0',
    }

    # Добавляем cookies для YouTube, если доступны
    if url_type in ['youtube', 'youtube_music']:
        for cookies_file in COOKIES_FILES:
            if os.path.exists(cookies_file):
                ydl_opts['cookiefile'] = cookies_file
                break

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=True)
            title = info.get('title', 'audio')
            filename = ydl.prepare_filename(info)

            # Меняем расширение на mp3
            base_name = os.path.splitext(filename)[0]
            filename = base_name + '.mp3'

            return filename, title
    except Exception as e:
        logger.error(f"Ошибка при скачивании аудио: {e}")
        raise e

# Функция поиска на YouTube Music
def search_youtube_music(query, max_results=5):
    """Выполняет поиск на YouTube Music и возвращает результаты"""
    ydl_opts = {
        'quiet': True,
        'no_warnings': True,
        'extract_flat': True,
        'skip_download': True,
        # Добавляем параметры для работы с SSL
        'no_check_certificate': True,
        'socket_timeout': 30,
        'source_address': '0.0.0.0',
    }

    # Добавляем cookies для YouTube, если доступны
    for cookies_file in COOKIES_FILES:
        if os.path.exists(cookies_file):
            ydl_opts['cookiefile'] = cookies_file
            break

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            # Используем обычный поиск YouTube с фильтрацией
            info = ydl.extract_info(f"ytsearch{max_results}:{query}", download=False)

            if not info or 'entries' not in info:
                return None

            return info['entries']
    except Exception as e:
        logger.error(f"Ошибка при поиске на YouTube Music: {e}")
        logger.error(traceback.format_exc())
        return None

# Функция добавления пользователя
def add_user(user_id, username, first_name, last_name):
    """Добавляет пользователя в база данных"""
    if str(user_id) not in user_data:
        user_data[str(user_id)] = {
            'username': username,
            'first_name': first_name,
            'last_name': last_name,
            'join_date': datetime.now().isoformat(),
            'download_count': 0
        }
        save_user_data()
    # Добавляем проверку для существующих пользователей
    elif 'download_count' not in user_data[str(user_id)]:
        user_data[str(user_id)]['download_count'] = 0
        save_user_data()

# Функция для обновления позиций в очереди
def update_queue_positions():
    """Обновляет позиции в очереди для всех пользователей"""
    global queue_status

    # Создаем временную очередь для анализа
    temp_queue = []
    while not download_queue.empty():
        try:
            task = download_queue.get_nowait()
            temp_queue.append(task)
            download_queue.task_done()
        except:
            break

    # Восстанавливаем очередь и обновляем позиции
    for i, task in enumerate(temp_queue):
        user_id, url, format_type, format_id, url_type, message, is_inline = task
        queue_status[user_id] = i + 1  # Позиция в очереди (начиная с 1)
        asyncio.create_task(download_queue.put(task))

async def monitor_download_size(file_path, message, max_size=50*1024*1024):  # 50 МБ
    """Мониторит размер файла во время загрузки и прерывает, если превышен лимит"""
    check_interval = 2  # Проверять каждые 2 секунды
    last_size = 0
    same_size_count = 0

    while True:
        await asyncio.sleep(check_interval)

        if not os.path.exists(file_path):
            continue

        current_size = os.path.getsize(file_path)

        # Если размер не меняется 3 раза подряд, возможно загрузка завершена
        if current_size == last_size:
            same_size_count += 1
            if same_size_count >= 3:
                break
        else:
            same_size_count = 0
            last_size = current_size

        # Проверяем, не превышен ли лимит
        if current_size > max_size:
            try:
                # Пытаемся удалить файл
                if os.path.exists(file_path):
                    os.remove(file_path)
                await message.edit_text(
                    f"❌ Файл слишком большой для Telegram (уже {current_size//1024//1024} МБ).\n\n"
                    "Загрузка прервана. Попробуйте выбрать другое качество."
                )
                return False
            except Exception as e:
                logger.error(f"Ошибка при удалении большого файла: {e}")
                return False

        # Обновляем статус каждые 10 МБ
        if current_size // (10*1024*1024) != last_size // (10*1024*1024):
            try:
                await message.edit_text(f"⏳ Загружено: {current_size//1024//1024} МБ...")
            except:
                pass

    return True

async def process_download_queue(app):
    """Обрабатывает очередь загрузок"""
    global queue_processing
    queue_processing = True

    while not download_queue.empty():
        # Получаем задание из очереди
        task = await download_queue.get()
        user_id, url, format_type, format_id, url_type, message, is_inline = task

        try:
            # Обновляем статус для всех пользователей
            update_queue_positions()

            # Функция для безопасного редактирования сообщения
            async def safe_edit_message(text, retry=True):
                try:
                    if message and hasattr(message, 'edit_text'):
                        await message.edit_text(text)
                    else:
                        # Если сообщение недоступно, отправляем новое
                        new_message = await app.bot.send_message(chat_id=user_id, text=text)
                        return new_message
                except Exception as e:
                    logger.warning(f"Не удалось отредактировать сообщение: {e}")
                    if retry:
                        # Пытаемся отправить новое сообщение
                        try:
                            new_message = await app.bot.send_message(chat_id=user_id, text=text)
                            return new_message
                        except Exception as send_error:
                            logger.error(f"Не удалось отправить сообщение пользователю {user_id}: {send_error}")
                    return None


			async def safe_send_file(file_path, title, is_audio, source_text, is_inline_mode=False):
				"""Безопасная отправка файла с учетом режима (инлайн или обычный)"""
				try:
					with open(file_path, 'rb') as file:

						if is_inline_mode:

							target_chat_id = user_id
						else:
							if message and hasattr(message, 'chat_id'):
								target_chat_id = message.chat_id
							else:
								target_chat_id = user_id

						if is_audio:
							return await asyncio.wait_for(
								app.bot.send_audio(
									chat_id=target_chat_id,
									audio=file,
									caption=f"🎵 {title}",
									title=title[:30] + "..." if len(title) > 30 else title,
									performer=source_text
								),
								timeout=SEND_FILE_TIMEOUT
							)
						else:
							return await asyncio.wait_for(
								app.bot.send_video(
									chat_id=target_chat_id,
									video=file,
									caption=f"🎥 {title}\n📺 Источник: {source_text}",
									supports_streaming=True
								),
								timeout=SEND_FILE_TIMEOUT
							)
				except asyncio.TimeoutError:
					raise
				except Exception as e:
					logger.error(f"Ошибка при отправке файла: {e}")
					raise


            # Уведомляем пользователя о начале обработки
            await safe_edit_message("⏳ Начинаю загрузку...")

            # Выполняем загрузку асинхронно
            try:
                if format_type == "tiktok" or url_type == "tiktok":
                    filename, title = await download_video_async(url, "best", None, url_type, message)
                elif format_type == "best":
                    filename, title = await download_video_async(url, "best", None, url_type, message)
                elif format_type == "max":
                    filename, title = await download_video_async(url, "max", None, url_type, message)
                elif format_type == "audio":
                    filename, title = await download_audio_async(url, url_type, message)
                else:
                    filename, title = await download_video_async(url, format_type, format_id, url_type, message)
            except Exception as e:
                if "Файл слишком большой" in str(e):
                    error_text = (
                        f"❌ Файл слишком большой для Telegram (превышает 50 МБ).\n\n"
                        "Попробуйте выбрать другое качество."
                    )
                else:
                    error_text = "❌ Произошла ошибка при загрузке видео. Пожалуйста, попробуйте позже."

                await safe_edit_message(error_text)
                continue

            file_size = os.path.getsize(filename)

            if file_size > 50 * 1024 * 1024:
                os.remove(filename)
                await safe_edit_message(
                    f"❌ Файл слишком большой для Telegram ({file_size//1024//1024} МБ).\n\n"
                    "Попробуйте выбрать другое качество."
                )
                continue

            is_audio = filename.endswith(('.mp3', '.m4a', '.ogg', '.wav'))

            if url_type == "youtube_music":
                source_text = "YouTube Music"
            elif url_type == "tiktok":
                source_text = "TikTok"
            else:
                source_text = "YouTube"

            await safe_edit_message("📤 Отправляю файл...")

            try:
                await safe_send_file(filename, title, is_audio, source_text, is_inline)
            except asyncio.TimeoutError:
                await safe_edit_message("❌ Таймаут при отправке файла. Пожалуйста, попробуйте позже.")
                continue
            except Exception as e:
                logger.error(f"Ошибка при отправке файла: {e}")
                await safe_edit_message("❌ Ошибка при отправке файла. Пожалуйста, попробуйте позже.")
                continue

            # Добавляем в кэш (только для видео)
            if not is_audio:
                # Получаем информацию о формате для качества
                quality = "best"
                if format_type != "best" and format_type != "tiktok" and format_type != "max":
                    # Находим информацию о формате
                    if user_id in user_videos and 'formats' in user_videos[user_id]:
                        for fmt in user_videos[user_id]['formats']:
                            if fmt.get('format_id') == format_id:
                                quality = f"{fmt.get('height', 'unknown')}p"
                                break

                add_to_video_cache(url, filename, format_id, quality,
                                  user_videos[user_id].get('duration', 0) if user_id in user_videos else 0,
                                  title, url_type)
            else:
                os.remove(filename)  # Аудио не кэшируем

            # Увеличиваем счетчик загрузок пользователя
            if str(user_id) in user_data:
                if 'download_count' not in user_data[str(user_id)]:
                    user_data[str(user_id)]['download_count'] = 0
                user_data[str(user_id)]['download_count'] += 1
                save_user_data()

            if is_inline:
                if message and hasattr(message, 'delete'):
                    try:
                        await message.delete()
                    except:
                        pass
            else:
                await safe_edit_message("✅ Готово! Что-нибудь еще?")

            if user_id in user_videos:
                del user_videos[user_id]

            # Удаляем пользователя из очереди
            if user_id in queue_status:
                del queue_status[user_id]

        except Exception as e:
            logger.error(f"Ошибка при обработке задания из очереди: {e}")
            logger.error(traceback.format_exc())
            try:
                await safe_edit_message("❌ Произошла ошибка при загрузке видео. Пожалуйста, попробуйте позже.")
            except:
                pass

            # Отправляем сообщение об ошибке администратору
            try:
                if ADMIN_ID:
                    error_text = f"❌ Ошибка при обработке задания из очереди:\n\n{str(e)[:1000]}"
                    await app.bot.send_message(chat_id=ADMIN_ID, text=error_text)
            except Exception as admin_error:
                logger.error(f"Ошибка при отправке сообщения администратору: {admin_error}")

        # Обновляем позиции в очереди после завершения задания
        update_queue_positions()
        await asyncio.sleep(1)  # Небольшая пауза между заданиями

    queue_processing = False

# Команда /start
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик команды /start"""
    chat = update.effective_chat
    user = update.effective_user
    add_user(user.id, user.username, user.first_name, user.last_name)

    # Разные приветственные сообщения для групп и личных чатов
    if chat.type in ['group', 'supergroup']:
        welcome_text = (
            "👋 Привет! Я бот для скачивания видео с YouTube, YouTube Music и TikTok.\n\n"
            "📹 Просто отправьте мне ссылку на видео в этом чате, и я скачаю его для вас!\n\n"
            "✨ Особенности:\n"
            "• Поддержка YouTube, YouTube Music и TikTok\n"
            "• Выбор качества видео\n"
            "• Скачивание аудио (команда /audio)\n"
            "• Поиск музыки (команда /search)\n"
            "• Автоматическое кэширование\n"
            "• Быстрая загрузка\n\n"
            "🚀 Отправьте мне ссылку и попробуйте!\n\n"
            "🐝 Автор бота @hairpin00"
            "🧱 Автор аватарки бота @CatMaxwellHi"
        )
    else:
        welcome_text = (
            "👋 Привет! Я бот для скачивания видео с YouTube, YouTube Music и TikTok.\n\n"
            "📹 Просто отправь мне ссылку на видео, и я скачаю его для тебя!\n\n"
            "✨ Особенности:\n"
            "• Поддержка YouTube, YouTube Music и TikTok\n"
            "• Выбор качества видео\n"
            "• Скачивание аудио (команда /audio)\n"
            "• Поиск музыки (команда /search)\n"
            "• Автоматическое кэширование\n"
            "• Быстрая загрузка\n\n"
            "🚀 Отправь мне ссылку и попробуй!\n\n"
            "🐝 Автор бота @hairpin00\n"
            "🧱 Автор аватарки бота @CatMaxwellHi"
        )

    await update.message.reply_text(welcome_text)

# Команда /help
async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик команды /help"""
    chat = update.effective_chat

    # Разные справки для групп и личных чатов
    if chat.type in ['group', 'supergroup']:
        help_text = (
            "📖 Справка по использованию бота в группе:\n\n"
            "1. 📹 Для скачивания видео просто отправьте ссылку на видео с YouTube, YouTube Music или TikTok\n"
            "2. 🎵 Для скачивания только аудио используйте команду /audio [ссылка]\n"
            "3. 🔍 Для поиска музыки используйте команду /search [запрос]\n"
            "4. ⚙️ Бот автоматически предложит выбрать качество видео\n"
            "5. 📦 Часто запрашиваемые видео сохраняются в кэше для быстрого доступа\n\n"
            "📝 Примеры ссылок:\n"
            "• YouTube: https://www.youtube.com/watch?v=VIDEO_ID\n"
            "• YouTube Music: https://music.youtube.com/watch?v=VIDEO_ID\n"
            "• TikTok: https://www.tiktok.com/@username/video/VIDEO_ID\n\n"
            "⚠️ Ограничения:\n"
            "• Максимальный размер файла: 50 МБ (ограничение Telegram)\n"
            "• Некоторые видео могут быть недоступны из-за ограничений платформ"
        )
    else:
        help_text = (
            "📖 Справка по использованию бота:\n\n"
            "1. 📹 Для скачивания видео просто отправьте ссылку на видео с YouTube, YouTube Music или TikTok\n"
            "2. 🎵 Для скачивания только аудио используйте команду /audio [ссылка]\n"
            "3. 🔍 Для поиска музыки используйте команду /search [запрос]\n"
            "4. ⚙️ Бот автоматически предложит выбрать качество видео\n"
            "5. 📦 Часто запрашиваемые видео сохраняются в кэше для быстрого доступа\n\n"
            "📝 Примеры ссылок:\n"
            "• YouTube: https://www.youtube.com/watch?v=VIDEO_ID\n"
            "• YouTube Music: https://music.youtube.com/watch?v=VIDEO_ID\n"
            "• TikTok: https://www.tiktok.com/@username/video/VIDEO_ID\n\n"
            "⚠️ Ограничения:\n"
            "• Максимальный размер файла: 50 МБ (ограничение Telegram)\n"
            "• Некоторые видео могут быть недоступны из-за ограничений платформ"
        )

    await update.message.reply_text(help_text)

# Команда /stats
async def stats_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик команды /stats (только для админа)"""
    user_id = update.effective_user.id
    if str(user_id) != str(ADMIN_ID):
        await update.message.reply_text("❌ У вас нет прав для выполнения этой команды.")
        return

    # Получаем размер кэша
    cache_size = 0
    if os.path.exists(CACHE_DIR):
        for path, dirs, files in os.walk(CACHE_DIR):
            for f in files:
                fp = os.path.join(path, f)
                cache_size += os.path.getsize(fp)

    stats_text = (
        f"📊 Статистика бота:\n\n"
        f"• Пользователей: {len(user_data)}\n"
        f"• Видео в кэше: {len(load_video_cache())}\n"
        f"• Размер кэша: {cache_size//1024//1024} МБ\n"
        f"• Заданий в очереди: {download_queue.qsize()}"
    )
    await update.message.reply_text(stats_text)

# Команда /broadcast
async def broadcast_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик команды /broadcast (только для админа)"""
    user_id = update.effective_user.id
    if str(user_id) != str(ADMIN_ID):
        await update.message.reply_text("❌ У вас нет прав для выполнения этой команды.")
        return

    if not context.args:
        await update.message.reply_text("❌ Укажите сообщение для рассылки.")
        return

    message = " ".join(context.args)
    success_count = 0
    fail_count = 0

    for user_id_str in user_data.keys():
        try:
            await context.bot.send_message(chat_id=user_id_str, text=f"📢 Рассылка:\n\n{message}")
            success_count += 1
            await asyncio.sleep(0.1)  # Чтобы не превысить лимиты Telegram
        except Exception as e:
            fail_count += 1
            logger.error(f"Ошибка при отправке сообщения пользователю {user_id_str}: {e}")

    await update.message.reply_text(
        f"✅ Рассылка завершена:\n"
        f"• Успешно: {success_count}\n"
        f"• Не удалось: {fail_count}"
    )

# Команда /audio
async def audio_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик команды /audio"""
    if not context.args:
        await update.message.reply_text("❌ Пожалуйста, укажите ссылку после команды /audio")
        return

    url = context.args[0]
    user = update.effective_user
    user_id = user.id

    # Добавляем пользователя в базу
    add_user(user_id, user.username, user.first_name, user.last_name)

    # Определяем тип ссылки
    url_type = get_url_type(url)

    if url_type == 'unknown':
        await update.message.reply_text(
            "❌ Это не похоже на поддерживаемую ссылку.\n\n"
            "📝 Примеры поддерживаемых ссылок:\n\n"
            "YouTube:\n"
            "- https://www.youtube.com/watch?v=VIDEO_ID\n"
            "- https://youtu.be/VIDEO_ID\n\n"
            "YouTube Music:\n"
            "- https://music.youtube.com/watch?v=VIDEO_ID\n"
            "- https://music.youtube.com/playlist?list=PLAYLIST_ID\n\n"
            "TikTok:\n"
            "- https://www.tiktok.com/@username/video/VIDEO_ID\n"
            "- https://vm.tiktok.com/VIDEO_ID\n"
        )
        return

    # Добавляем задание в очередь
    task = (user_id, url, "audio", None, url_type, update.message, False)
    await download_queue.put(task)

    # Обновляем позиции в очереди
    update_queue_positions()

    # Сообщаем пользователю о позиции в очереди
    position = queue_status.get(user_id, 0)
    if position > 0:
        await update.message.reply_text(f"📋 Ваш запрос на аудио добавлен в очередь. Позиция: {position}")
    else:
        await update.message.reply_text("📋 Ваш запрос на аудио добавлен в очередь.")

    # Запускаем обработку очереди, если она не активна
    if not queue_processing:
        asyncio.create_task(process_download_queue(context.application))
# Команда /search - начало поиска
async def search_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик команды /search - начало процесса поиска"""
    user = update.effective_user
    add_user(user.id, user.username, user.first_name, user.last_name)

    if not context.args:
        # Используем безопасный метод отправки сообщения
        if update.effective_message:
            await update.effective_message.reply_text(
                "🔍 Пожалуйста, укажите запрос для поиска.\n\n"
                "Пример: /search Coldplay Yellow"
            )
        else:
            # Если нет сообщения, отправляем через контекст
            await context.bot.send_message(
                chat_id=update.effective_chat.id,
                text="🔍 Пожалуйста, укажите запрос для поиска.\n\n"
                     "Пример: /search Coldplay Yellow"
            )
        return ConversationHandler.END

    query = " ".join(context.args)
    return await execute_search(update, context, query)

async def execute_search(update: Update, context: ContextTypes.DEFAULT_TYPE, query):
    user = update.effective_user
    user_id = user.id

    if len(query) > MAX_SEARCH_LENGTH:
        if update.effective_message:
            await update.effective_message.reply_text(f"❌ Запрос слишком длинный. Максимально: {MAX_SEARCH_LENGTH} символов.")
        else:
            await context.bot.send_message(
                chat_id=update.effective_chat.id,
                text=f"❌ Запрос слишком длинный. Максимально: {MAX_SEARCH_LENGTH} символов."
            )
        return ConversationHandler.END

    current_time = time.time()
    last_time = last_search_time.get(user_id, 0)

    if current_time - last_time < MIN_SEARCH_INTERVAL:
        wait_time = MIN_SEARCH_INTERVAL - int(current_time - last_time)
        if update.effective_message:
            await update.effective_message.reply_text(f"⏳ Подождите {wait_time} секунд перед следующим поиском.")
        else:
            await context.bot.send_message(
                chat_id=update.effective_chat.id,
                text=f"⏳ Подождите {wait_time} секунд перед следующим поиском."
            )
        return ConversationHandler.END

    last_search_time[user_id] = current_time

    if update.effective_message:
        search_msg = await update.effective_message.reply_text(f"🔍 Ищу \"{query[:50]}\"...")
    else:
        search_msg = await context.bot.send_message(
            chat_id=update.effective_chat.id,
            text=f"🔍 Ищу \"{query[:50]}\"..."
        )

    try:
        loop = asyncio.get_event_loop()

        try:
            results = await asyncio.wait_for(
                loop.run_in_executor(download_executor, search_youtube_music, query),
                timeout=SEARCH_TIMEOUT
            )
        except asyncio.TimeoutError:
            await search_msg.edit_text("❌ Поиск занял слишком много времени. Попробуйте позже.")
            return ConversationHandler.END

        if not results:
            await search_msg.edit_text("❌ По вашему запросу ничего не найдено.")
            return ConversationHandler.END

        user_searches[user_id] = {
            'query': query,
            'results': results,
            'timestamp': time.time()
        }

        keyboard = []
        for i, result in enumerate(results[:5]):
            title = result.get('title', 'Без названия')
            duration = result.get('duration', 0)
            uploader = result.get('uploader', 'Неизвестный исполнитель')

            if duration:
                minutes = int(duration // 60)
                seconds = int(duration % 60)
                duration_str = f"{minutes}:{seconds:02d}"
            else:
                duration_str = "??:??"

            button_text = f"{i+1}. {uploader} | {title} ({duration_str})"
            if len(button_text) > 60:
                button_text = button_text[:57] + "..."

            keyboard.append([InlineKeyboardButton(
                button_text,
                callback_data=f"search_result:{i}:{user_id}"
            )])

        keyboard.append([InlineKeyboardButton("❌ Отмена", callback_data=f"search_cancel:{user_id}")])

        reply_markup = InlineKeyboardMarkup(keyboard)

        await search_msg.edit_text(
            f"🎵 Найдено результатов по запросу \"{query[:50]}\":\n\nВыберите трек:",
            reply_markup=reply_markup
        )

        return SEARCH_RESULT

    except Exception as e:
        logger.error(f"Ошибка при поиске: {e}")
        await search_msg.edit_text("❌ Произошла ошибка при поиске.")
        return ConversationHandler.END

async def handle_search_result(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        query = update.callback_query
        await query.answer()

        data = query.data
        parts = data.split(":")

        if len(parts) < 3:
            await query.edit_message_text("❌ Ошибка в данных запроса.")
            return ConversationHandler.END

        action = parts[0]

        if action == "search_cancel":
            user_id = int(parts[1])
            await query.edit_message_text("❌ Поиск отменен.")
            if user_id in user_searches:
                del user_searches[user_id]
            return ConversationHandler.END

        result_index = int(parts[1])
        user_id = int(parts[2])

        if user_id not in user_searches:
            await query.edit_message_text("❌ Результаты поиска устарели.")
            return ConversationHandler.END

        search_data = user_searches[user_id]
        results = search_data.get('results', [])

        if result_index >= len(results):
            await query.edit_message_text("❌ Выбранный результат больше не доступен.")
            return ConversationHandler.END

        selected_result = results[result_index]
        url = selected_result.get('url')
        title = selected_result.get('title', 'Выбранный трек')

        if not url:
            await query.edit_message_text("❌ Не удалось получить ссылку на трек.")
            return ConversationHandler.END

        await query.edit_message_text(f"⏳ Получаю информацию о треке...")

        try:
            info = get_video_info(url, 'youtube')
            formats = info.get('formats', [])

            if not formats:
                await query.edit_message_text("❌ Не удалось получить информацию о треке.")
                return ConversationHandler.END

            keyboard = create_quality_keyboard(formats, url, user_id, 'youtube')
            duration = info.get('duration', 0)

            minutes = int(duration // 60)
            seconds = int(duration % 60)
            hours, minutes = divmod(minutes, 60)
            if hours > 0:
                duration_str = f"{hours}:{minutes:02d}:{seconds:02d}"
            else:
                duration_str = f"{minutes}:{seconds:02d}"

            await query.edit_message_text(
                f"🎵 {title}\n⏱ Длительность: {duration_str}\n📺 Источник: YouTube\n\nВыберите качество:",
                reply_markup=keyboard
            )

            user_videos[user_id] = {
                'url': url,
                'formats': formats,
                'url_type': 'youtube',
                'title': title,
                'duration': duration
            }

            return ConversationHandler.END

        except Exception as e:
            logger.error(f"Ошибка при получении информации о треке: {e}")
            await query.edit_message_text("❌ Произошла ошибка.")
            return ConversationHandler.END

    except Exception as e:
        logger.error(f"Ошибка в обработке выбора поиска: {e}")
        return ConversationHandler.END


async def cancel_search(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик отмена поиска"""
    user = update.effective_user
    user_id = user.id

    if user_id in user_searches:
        del user_searches[user_id]

    await update.message.reply_text("❌ Поиск отменен.")
    return ConversationHandler.END

# Команда /queue
async def queue_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик команды /queue для просмотра статуса очереди"""
    user_id = update.effective_user.id

    if download_queue.empty():
        await update.message.reply_text("📋 Очередь загрузок пуста.")
    else:
        position = queue_status.get(user_id, 0)
        if position > 0:
            await update.message.reply_text(f"📋 Ваша позиция в очереди: {position}\nВсего заданий в очереди: {download_queue.qsize()}")
        else:
            await update.message.reply_text(f"📋 У вас нет активных заданий в очереди.\nВсего заданий в очереди: {download_queue.qsize()}")

class DownloadProgress:
    def __init__(self, message, max_size=50*1024*1024):
        self.message = message
        self.max_size = max_size
        self.last_update = 0
        self.start_time = time.time()
        self.loop = None

    def progress_hook(self, d):
        if d['status'] == 'downloading':
            # Получаем информацию о прогрессе
            total_bytes = d.get('total_bytes') or d.get('total_bytes_estimate')
            downloaded_bytes = d.get('downloaded_bytes', 0)

            # Проверяем размер
            if downloaded_bytes > self.max_size:
                raise Exception(f"File size exceeded {self.max_size} bytes")

            # Обновляем сообщение не чаще чем раз в 5 секунд
            current_time = time.time()
            if current_time - self.last_update >= 5:
                if total_bytes:
                    percent = (downloaded_bytes / total_bytes) * 100
                    speed = d.get('speed', 0)
                    eta = d.get('eta', 0)

                    # Форматируем информацию
                    size_mb = downloaded_bytes / 1024 / 1024
                    total_mb = total_bytes / 1024 / 1024
                    speed_mb = speed / 1024 / 1024 if speed else 0

                    status_text = (
                        f"⏳ Загружаю: {percent:.1f}%\n"
                        f"📊 {size_mb:.1f} / {total_mb:.1f} МБ\n"
                        f"🚀 Скорость: {speed_mb:.1f} МБ/с\n"
                        f"⏱ Осталось: {eta} сек"
                    )
                else:
                    size_mb = downloaded_bytes / 1024 / 1024
                    status_text = f"⏳ Загружено: {size_mb:.1f} МБ..."

                try:
                    # Используем asyncio для планирования задачи в основном потоке
                    if self.loop:
                        asyncio.run_coroutine_threadsafe(self.update_message(status_text), self.loop)
                except:
                    pass

                self.last_update = current_time

    def set_loop(self, loop):
        """Устанавливает цикл событий для асинхронных вызовов"""
        self.loop = loop

    async def update_message(self, text):
        try:
            await self.message.edit_text(text)
        except Exception as e:
            logger.debug(f"Не удалось обновить сообщение прогресса: {e}")

# Обработчик ошибок
async def error_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик ошибки"""
    logger.error(msg="Exception while handling an update:", exc_info=context.error)

    # Отправляем сообщение об ошибке администратору
    try:
        if ADMIN_ID:
            error_text = f"❌ Ошибка в боте:\n\n{context.error}\n\n{traceback.format_exc()}"
            await context.bot.send_message(chat_id=ADMIN_ID, text=error_text[:4000])
    except Exception as e:
        logger.error(f"Ошибка при отправке сообщения администратору: {e}")


async def handle_inline_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик для inline-кнопок"""
    try:
        query = update.callback_query
        await query.answer()

        data = query.data
        logger.info(f"Обрабатываем inline callback: {data}")

        # Исправляем разбор данных - разделяем только по первому двоеточию
        if data.startswith("inline_cache:"):
            cache_key = data[13:]  # "inline_cache:".length = 13
            action = "inline"
            # Получаем URL из кэша
            cached_data = get_cached_query(cache_key)
            if not cached_data:
                await query.edit_message_text("❌ Время жизни запроса истекло. Пожалуйста, выполните запрос снова.")
                return
            url = cached_data['url']
        elif data.startswith("audio_cache:"):
            cache_key = data[12:]  # "audio_cache:".length = 12
            action = "audio_inline"
            # Получаем URL из кэша
            cached_data = get_cached_query(cache_key)
            if not cached_data:
                await query.edit_message_text("❌ Время жизни запроса истекло. Пожалуйста, выполните запрос снова.")
                return
            url = cached_data['url']
        else:
            # Старый формат для обратной совместимости
            if data.startswith("inline:"):
                url = data[7:]
                action = "inline"
            elif data.startswith("audio_inline:"):
                url = data[13:]
                action = "audio_inline"
            else:
                await query.edit_message_text("❌ Неизвестный формат запроса.")
                return

        user = update.effective_user
        user_id = user.id

        # Добавляем пользователя в базу
        add_user(user_id, user.username, user.first_name, user.last_name)

        # Определяем тип ссылки
        url_type = get_url_type(url)
        logger.info(f"URL: {url}, тип: {url_type}")

        if url_type == 'unknown':
            await query.edit_message_text("❌ Неподдерживаемая ссылка.")
            return

        if action == "inline":
            await query.edit_message_text("⏳ Получаю информацию о видео...")

            try:
                info = get_video_info(url, url_type)
                formats = info.get('formats', [])

                if not formats:
                    await query.edit_message_text("❌ Не удалось получить информацию о видео.")
                    return

                # Для TikTok добавляем в очередь
                if url_type == 'tiktok':
                    task = (user_id, url, "best", None, url_type, query.message, True)
                    await download_queue.put(task)

                    update_queue_positions()

                    position = queue_status.get(user_id, 0)
                    if position > 0:
                        await query.edit_message_text(f"📋 Ваш запрос добавлен в очередь. Позиция: {position}")
                    else:
                        await query.edit_message_text("📋 Ваш запрос добавлен в очередь.")

                    if not queue_processing:
                        asyncio.create_task(process_download_queue(context.application))
                    return

                # Для YouTube и YouTube Music показываем выбор качества
                keyboard = create_quality_keyboard(formats, url, user_id, url_type, is_inline=True)
                title = info.get('title', 'YouTube видео')
                duration = info.get('duration', 0)

                minutes = int(duration // 60)
                seconds = int(duration % 60)
                hours, minutes = divmod(minutes, 60)
                if hours > 0:
                    duration_str = f"{hours}:{minutes:02d}:{seconds:02d}"
                else:
                    duration_str = f"{minutes}:{seconds:02d}"

                # Правильно определяем источник
                if url_type == "youtube_music":
                    source_text = "YouTube Music"
                elif url_type == "tiktok":
                    source_text = "TikTok"
                else:
                    source_text = "YouTube"

                await query.edit_message_text(
                    f"🎬 {title}\n⏱ Длительность: {duration_str}\n📺 Источник: {source_text}\n\nВыберите качество:",
                    reply_markup=keyboard
                )

                # Сохраняем информацию о видео для пользователя
                user_videos[user_id] = {
                    'url': url,
                    'formats': formats,
                    'url_type': url_type,
                    'title': title,
                    'duration': duration
                }

            except Exception as e:
                logger.error(f"Ошибка при получении информации о видео: {e}")
                logger.error(traceback.format_exc())
                await query.edit_message_text("❌ Произошла ошибка. Пожалуйста, попробуйте позже.")

        elif action == "audio_inline":
            # Обработка аудио из inline-запроса
            # Добавляем задание в очередь
            task = (user_id, url, "audio", None, url_type, query.message, True)
            await download_queue.put(task)

            # Обновляем позиции в очереди
            update_queue_positions()

            # Сообщаем пользователю о позиции в очереди
            position = queue_status.get(user_id, 0)
            if position > 0:
                await query.edit_message_text(f"📋 Ваш запрос на аудио добавлен в очередь. Позиция: {position}")
            else:
                await query.edit_message_text("📋 Ваш запрос на аудио добавлен в очередь.")

            # Запускаем обработку очереди, если она не активна
            if not queue_processing:
                asyncio.create_task(process_download_queue(context.application))

    except Exception as e:
        logger.error(f"Ошибка в обработке inline callback: {e}")
        logger.error(traceback.format_exc())


async def inline_query_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Обработчик inline-запросов"""
    try:
        query = update.inline_query.query
        if not query:
            return

        # Очищаем старый кэш
        clean_old_cache()

        # Проверяем, является ли запрос URL
        url_type = get_url_type(query)
        if url_type == 'unknown':
            return

        # Получаем информацию о видео
        try:
            info = get_video_info(query, url_type)
            title = info.get('title', 'Видео')
            thumbnail = info.get('thumbnail', '')
            duration = info.get('duration', 0)

            # Обрезаем длинное название
            if len(title) > 30:
                title_display = title[:27] + "..."
            else:
                title_display = title

            # Создаем результаты для inline-запроса
            results = []

            # Генерируем ключи кэша для каждого варианта
            video_cache_key = cache_inline_query(query, 'inline')
            audio_cache_key = cache_inline_query(query, 'audio_inline')

            # Вариант для видео
            results.append(
                InlineQueryResultArticle(
                    id='1',
                    title=f"🎥 {title_display}",
                    description="Скачать видео",
                    input_message_content=InputTextMessageContent(
                        f"🎥 Запрос на скачивание видео\n\nНажмите кнопку ниже для выбора качества.",
                        parse_mode=None
                    ),
                    # Используем ключ кэша вместо полного URL
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("🔄 Обработать видео", callback_data=f"inline_cache:{video_cache_key}")]
                    ]),
                    thumbnail_url=thumbnail
                )
            )

            # Вариант для аудио (только для YouTube и YouTube Music)
            if url_type in ['youtube', 'youtube_music']:
                results.append(
                    InlineQueryResultArticle(
                        id='2',
                        title=f"🎵 {title_display}",
                        description="Скачать только аудио",
                        input_message_content=InputTextMessageContent(
                            f"🎵 Запрос на скачивание аудио",
                            parse_mode=None
                        ),
                        # Используем ключ кэша вместо полного URL
                        reply_markup=InlineKeyboardMarkup([
                            [InlineKeyboardButton("🔄 Обработать аудио", callback_data=f"audio_cache:{audio_cache_key}")]
                        ]),
                        thumbnail_url=thumbnail
                    )
                )

            await update.inline_query.answer(results, cache_time=1)

        except Exception as e:
            logger.error(f"Ошибка при обработке inline-запроса: {e}")
            logger.error(traceback.format_exc())

    except Exception as e:
        logger.error(f"Ошибка в inline_query_handler: {e}")
        logger.error(traceback.format_exc())

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        user = update.effective_user
        chat = update.effective_chat
        text = update.message.text.strip()
        user_id = user.id

        # Добавляем пользователя в базу
        add_user(user_id, user.username, user.first_name, user.last_name)

        # Определяем тип ссылки
        url_type = get_url_type(text)

        if url_type == 'unknown':

            if chat.type in ['group', 'supergroup']:
                await update.message.reply_text(
                    "❌ Это не похоже на поддерживаемую ссылку."

                )
            else:
                await update.message.reply_text(
                    "❌ Это не похоже на прямую ссылку на видео YouTube, YouTube Music или TikTok.\n\n"
                    "📝 Примеры поддерживаемых ссылок:\n\n"
                    "YouTube:\n"
                    "- https://www.youtube.com/watch?v=VIDEO_ID\n"
                    "- https://youtu.be/VIDEO_ID\n"
                    "- https://www.youtube.com/shorts/VIDEO_ID\n\n"
                    "YouTube Music:\n"
                    "- https://music.youtube.com/watch?v=VIDEO_ID\n"
                    "- https://music.youtube.com/playlist?list=PLAYLIST_ID\n\n"
                    "TikTok:\n"
                    "- https://www.tiktok.com/@username/video/VIDEO_ID\n"
                    "- https://vm.tiktok.com/VIDEO_ID\n"
                    "- https://vt.tiktok.com/VIDEO_ID\n\n"
                    "⚠️ Ссылки на поиск, плейлисты или главные страницы не поддерживаются."
                )
            return

        # Проверяем кэш
        cached_versions = get_cached_versions(text)

        if cached_versions:
            status_msg = await update.message.reply_text("⏳ Проверяю кэш...")
            keyboard = create_cache_choice_keyboard(text, user_id, cached_versions)

            await status_msg.edit_text(
                f"🎬 Найдено {len(cached_versions)} кэшированных версий этого видео.\n\n"
                "Выберите действие:",
                reply_markup=keyboard
            )

            # Сохраняем информацию о видео для пользователя
            user_videos[user_id] = {'url': text, 'cached_versions': cached_versions, 'url_type': url_type}
            return

        status_msg = await update.message.reply_text("⏳ Получаю информацию о видео...")

        try:
            info = get_video_info(text, url_type)
            formats = info.get('formats', [])

            if not formats:
                await status_msg.edit_text("❌ Не удалось получить информацию о видео.")
                return

            # Для TikTok добавляем в очередь
            if url_type == 'tiktok':
                # Добавляем задание в очередь
                task = (user_id, text, "best", None, url_type, status_msg, False)
                await download_queue.put(task)

                # Обновляем позиции в очереди
                update_queue_positions()

                # Сообщаем пользователю о позиции в очереди
                position = queue_status.get(user_id, 0)
                if position > 0:
                    await status_msg.edit_text(f"📋 Ваш TikTok запрос добавлен в очередь. Позиция: {position}")
                else:
                    await status_msg.edit_text("📋 Ваш TikTok запрос добавлен в очередь.")

                # Запускаем обработку очереди, если она не активна
                if not queue_processing:
                    asyncio.create_task(process_download_queue(context.application))
                return


            keyboard = create_quality_keyboard(formats, text, user_id, url_type)
            title = info.get('title', 'YouTube видео')
            duration = info.get('duration', 0)

            minutes = int(duration // 60)
            seconds = int(duration % 60)
            hours, minutes = divmod(minutes, 60)
            if hours > 0:
                duration_str = f"{hours}:{minutes:02d}:{seconds:02d}"
            else:
                duration_str = f"{minutes}:{seconds:02d}"

            source_text = "YouTube Music" if url_type == "youtube_music" else "YouTube"

            await status_msg.edit_text(
                f"🎬 {title}\n⏱ Длительность: {duration_str}\n📺 Источник: {source_text}\n\nВыберите качество:",
                reply_markup=keyboard
            )


            user_videos[user_id] = {
                'url': text,
                'formats': formats,
                'url_type': url_type,
                'title': title,
                'duration': duration
            }

        except Exception as e:
            logger.error(f"Ошибка при получении информации о видео: {e}")
            logger.error(traceback.format_exc())
            error_msg = str(e).lower()

            if "unable to extract sigi state" in error_msg or "ошибка загрузки tiktok" in error_msg:
                await status_msg.edit_text(
                    "❌ В настоящее время загрузка видео с TikTok временно не работает из-за изменений на платформе.\n\n"
                    "Пожалуйста, попробуйте позже или используйте YouTube ссылки."
                )
            elif "cookies" in error_msg and "youtube" in error_msg:
                await status_msg.edit_text(
                    "❌ Для доступа к этому видео требуется авторизация YouTube.\n\n"
                    "Пожалуйста, попробуйте другую ссылку или обратитесь к администратору бота."
                )
            elif "unsupported url" in error_msg:
                await status_msg.edit_text(
                    "❌ Неподдерживаемая ссылка. Пожалуйста, убедитесь, что это прямая ссылка на видео, а не на страницу поиска или плейлист.\n\n"
                    "📝 Примеры поддерживаемых ссылок:\n"
                    "- YouTube: https://www.youtube.com/watch?v=VIDEO_ID\n"
                    "- YouTube Music: https://music.youtube.com/watch?v=VIDEO_ID\n"
                    "- TikTok: https://www.tiktok.com/@username/video/VIDEO_ID"
                )
            elif "decryption" in error_msg or "ssl" in error_msg:
                await status_msg.edit_text(
                    "❌ Произошла ошибка SSL при подключении. Пожалуйста, попробуйте позже или используйте VPN."
                )
            else:
                await status_msg.edit_text("❌ Произошла ошибка. Пожалуйста, попробуйте позже.")

    except Exception as e:
        logger.error(f"Ошибка в обработке сообщения: {e}")
        logger.error(traceback.format_exc())


async def handle_cache_selection(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        query = update.callback_query
        await query.answer()

        data = query.data
        parts = data.split(":")
        action = parts[0]  # cache или new_download

        # Исправляем обработку callback данных
        if action == "cache":
            if len(parts) < 3:
                await query.edit_message_text("❌ Ошибка в данных запроса.")
                return
            cache_index = int(parts[1])
            user_id = int(parts[2])
            is_inline = len(parts) > 3 and parts[3] == "inline"
        elif action == "new_download":
            if len(parts) < 2:
                await query.edit_message_text("❌ Ошибка в данных запроса.")
                return
            user_id = int(parts[1])
            is_inline = len(parts) > 2 and parts[2] == "inline"
        else:
            await query.edit_message_text("❌ Неизвестное действие.")
            return

        if user_id not in user_videos:
            await query.edit_message_text("❌ Информация о видео устарела.")
            return

        video_info = user_videos[user_id]
        url = video_info['url']
        url_type = video_info.get('url_type', 'youtube')

        if action == "cache":
            # Использование кэшированной версии
            cached_versions = video_info.get('cached_versions', [])

            if cache_index >= len(cached_versions):
                await query.edit_message_text("❌ Выбранная кэшированная версия больше не доступна.")
                return

            cache_data = cached_versions[cache_index]
            file_path = cache_data['file_path']

            if not os.path.exists(file_path):
                await query.edit_message_text("❌ Кэшированный файл больше не существует.")
                return

            await query.edit_message_text("📤 Отправляю кэшированное видео...")

            # Отправляем файл
            is_audio = file_path.endswith(('.mp3', '.m4a', '.ogg', '.wav'))
            title = cache_data.get('title', 'Video')
            source_text = "YouTube Music" if cache_data.get('url_type') == "youtube_music" else "YouTube"

            try:
                with open(file_path, 'rb') as file:
                    if is_audio:
                        await asyncio.wait_for(
                            context.bot.send_audio(
                                chat_id=query.message.chat_id,
                                audio=file,
                                caption=f"🎵 {title} (из кэша)",
                                title=title[:30] + "..." if len(title) > 30 else title,
                                performer=source_text
                            ),
                            timeout=SEND_FILE_TIMEOUT
                        )
                    else:
                        await asyncio.wait_for(
                            context.bot.send_video(
                                chat_id=query.message.chat_id,
                                video=file,
                                caption=f"🎥 {title} (из кэша)\n📺 Источник: {source_text}",
                                supports_streaming=True
                            ),
                            timeout=SEND_FILE_TIMEOUT
                        )
            except asyncio.TimeoutError:
                await query.edit_message_text("❌ Таймаут при отправке файла. Пожалуйста, попробуйте позже.")
                return

            if is_inline:
                await query.delete()
            else:
                await query.edit_message_text("✅ Готово! Что-нибудь еще?")

        elif action == "new_download":

            await query.edit_message_text("⏳ Получаю информацию о видео...")

            try:
                info = get_video_info(url, url_type)
                formats = info.get('formats', [])

                if not formats:
                    await query.edit_message_text("❌ Не удалось получить информацию о видео.")
                    return


                if url_type == 'tiktok':

                    task = (user_id, url, "best", None, url_type, query.message, is_inline)
                    await download_queue.put(task)


                    update_queue_positions()


                    position = queue_status.get(user_id, 0)
                    if position > 0:
                        await query.edit_message_text(f"📋 Ваш запрос добавлен в очередь. Позиция: {position}")
                    else:
                        await query.edit_message_text("📋 Ваш запрос добавлен в очередь.")


                    if not queue_processing:
                        asyncio.create_task(process_download_queue(context.application))
                    return


                keyboard = create_quality_keyboard(formats, url, user_id, url_type, is_inline)
                title = info.get('title', 'YouTube видео')
                duration = info.get('duration', 0)

                minutes = int(duration // 60)
                seconds = int(duration % 60)
                hours, minutes = divmod(minutes, 60)
                if hours > 0:
                    duration_str = f"{hours}:{minutes:02d}:{seconds:02d}"
                else:
                    duration_str = f"{minutes}:{seconds:02d}"

                source_text = "YouTube Music" if url_type == "youtube_music" else "YouTube"

                await query.edit_message_text(
                    f"🎬 {title}\n⏱ Длительность: {duration_str}\n📺 Источник: {source_text}\n\nВыберите качество:",
                    reply_markup=keyboard
                )

                # Сохраняем информацию о видео для пользователя
                user_videos[user_id] = {
                    'url': url,
                    'formats': formats,
                    'url_type': url_type,
                    'title': title,
                    'duration': duration
                }

            except Exception as e:
                logger.error(f"Ошибка при получении информации о видео: {e}")
                logger.error(traceback.format_exc())
                await query.edit_message_text("❌ Произошла ошибка. Пожалуйста, попробуйте позже.")

    except Exception as e:
        logger.error(f"Ошибка в обработке выбора кэша: {e}")
        logger.error(traceback.format_exc())


async def handle_quality_selection(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        query = update.callback_query
        await query.answer()

        data = query.data
        parts = data.split(":")
        format_type = parts[0]  # video, audio, best, max или tiktok

        # Унифицируем обработку разных форматов callback данных
        if format_type == "video":
            if len(parts) < 3:
                await query.edit_message_text("❌ Ошибка в данных запроса.")
                return
            format_id = parts[1]
            user_id = int(parts[2])
            is_inline = len(parts) > 3 and parts[3] == "inline"
        else:
            if len(parts) < 2:
                await query.edit_message_text("❌ Ошибка в данных запроса.")
                return
            format_id = None
            user_id = int(parts[1])
            is_inline = len(parts) > 2 and parts[2] == "inline"

        if user_id not in user_videos:
            await query.edit_message_text("❌ Информация о видео устарела.")
            return

        video_info = user_videos[user_id]
        url = video_info['url']
        url_type = video_info.get('url_type', 'youtube')

        # Добавляем задание в очередь
        task = (user_id, url, format_type, format_id, url_type, query.message, is_inline)
        await download_queue.put(task)

        # Обновляем позиции в очереди
        update_queue_positions()

        # Сообщаем пользователю о позиции в очереди
        position = queue_status.get(user_id, 0)
        if position > 0:
            await query.edit_message_text(f"📋 Ваш запрос добавлен в очередь. Позиция: {position}")
        else:
            await query.edit_message_text("📋 Ваш запрос добавлен в очередь.")

        # Запускаем обработку очереди, если она не активна
        if not queue_processing:
            asyncio.create_task(process_download_queue(context.application))

    except Exception as e:
        logger.error(f"Ошибка в обработке выбора качества: {e}")
        logger.error(traceback.format_exc())

# Добавляем команду для очистки кэша (только для админа)
async def clear_cache_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        user_id = update.effective_user.id

        # Проверяем, является ли пользователь администратором
        if str(user_id) != str(ADMIN_ID):
            await update.message.reply_text("❌ У вас нет прав для выполнения этой команды.")
            return

        # Очищаем кэш
        video_cache = load_video_cache()
        cache_size = 0
        deleted_files = 0

        for url_hash, cache_data in video_cache.items():
            file_path = cache_data.get('file_path', '')
            if os.path.exists(file_path):
                file_size = os.path.getsize(file_path)
                cache_size += file_size
                os.remove(file_path)
                deleted_files += 1

        # Очищаем файл кэша
        save_video_cache({})

        await update.message.reply_text(
            f"✅ Кэш очищен!\n"
            f"Удалено файлов: {deleted_files}\n"
            f"Освобождено места: {cache_size//1024//1024} МБ"
        )
    except Exception as e:
        logger.error(f"Ошибка в команде /clear_cache: {e}")
        logger.error(traceback.format_exc())

def main():

    load_user_data()
    load_subscriptions()

    application = Application.builder().token(BOT_TOKEN).read_timeout(30).write_timeout(30).connect_timeout(30).build()

    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("help", help_command))
    application.add_handler(CommandHandler("stats", stats_command))
    application.add_handler(CommandHandler("broadcast", broadcast_command))
    application.add_handler(CommandHandler("audio", audio_command))
    application.add_handler(CommandHandler("clear_cache", clear_cache_command))
    application.add_handler(CommandHandler("queue", queue_command))


    application.add_handler(CommandHandler("subscribe", subscribe_command))
    application.add_handler(CommandHandler("unsubscribe", unsubscribe_command))
    application.add_handler(CommandHandler("subscriptions", list_subscriptions_command))
    application.add_handler(CommandHandler("notifications", toggle_notifications_command))


    application.add_handler(CallbackQueryHandler(
        handle_subscription_callback,
        pattern="^(unsubscribe|unsubscribe_all|toggle_notif|manage_subs|toggle_menu|subscribe_dl):"
    ))


    search_handler = ConversationHandler(
        entry_points=[CommandHandler('search', search_command)],
        states={
            SEARCH_QUERY: [MessageHandler(filters.TEXT & ~filters.COMMAND, search_command)],
            SEARCH_RESULT: [CallbackQueryHandler(handle_search_result, pattern='^search_')]
        },
        fallbacks=[CommandHandler('cancel', cancel_search)]
    )
    application.add_handler(search_handler)


    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    application.add_handler(CallbackQueryHandler(handle_quality_selection, pattern="^(video|audio|best|max|tiktok):"))
    application.add_handler(CallbackQueryHandler(handle_cache_selection, pattern="^(cache|new_download):"))


    application.add_handler(CallbackQueryHandler(handle_inline_callback, pattern="^(inline|audio_inline):"))

    application.add_handler(InlineQueryHandler(inline_query_handler))
    application.add_error_handler(error_handler)
    application.add_handler(CallbackQueryHandler(handle_quality_selection, pattern="^(video|audio|best|max|tiktok):"))
    application.add_handler(CallbackQueryHandler(handle_cache_selection, pattern="^(cache|new_download):"))


    application.add_handler(CallbackQueryHandler(handle_inline_callback, pattern="^(inline|audio_inline|inline_cache|audio_cache):"))

    application.add_handler(InlineQueryHandler(inline_query_handler))


    logger.info("Бот запущен...")

	async def start_subscription_tasks(app):
			for user_id in subscriptions.keys():
				if user_id not in subscription_tasks:
					subscription_tasks[user_id] = asyncio.create_task(
						check_subscriptions_for_user(user_id, app)
					)

    try:
        loop = asyncio.get_event_loop()
        loop.create_task(start_subscription_tasks(application))
        application.run_polling(
            poll_interval=1.0,
            timeout=10,
            drop_pending_updates=True,
            allowed_updates=Update.ALL_TYPES
        )
    except KeyboardInterrupt:
        logger.info("Бот остановлен пользователем")

        for task in subscription_tasks.values():
            task.cancel()

        download_executor.shutdown(wait=True)
    except Exception as e:
        logger.error(f"Критическая ошибка: {e}")
        logger.error(traceback.format_exc())

        for task in subscription_tasks.values():
            task.cancel()
        download_executor.shutdown(wait=True)



if __name__ == "__main__":
    main()
