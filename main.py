from __future__ import annotations

import asyncio
import contextlib
import html
import io
import json
import logging
import os
import re
from collections import defaultdict, deque
from dataclasses import dataclass, field
from time import time
from typing import Any, Deque, Dict, Iterable, List, Optional, Sequence, Tuple
from urllib.parse import quote, quote_plus

import aiohttp
import yt_dlp
from dotenv import load_dotenv
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    ReplyKeyboardMarkup,
    Update,
)
from telegram.constants import ChatAction
from telegram.error import BadRequest
from telegram.ext import (
    AIORateLimiter,
    Application,
    ApplicationBuilder,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

load_dotenv()

# ============================================================
# Environment Helpers
# ============================================================

def env(name: str, default: str = "") -> str:
    value = os.getenv(name, default)
    return str(value).strip() if value is not None else ""


def env_int(name: str, default: int) -> int:
    try:
        return int(env(name, str(default)))
    except Exception:
        return default


def env_bool(name: str, default: bool = False) -> bool:
    raw = env(name, str(default)).lower()
    return raw in {"1", "true", "yes", "y", "on"}


def env_list(name: str) -> List[str]:
    raw = env(name, "")
    parts = re.split(r"[,\n]+", raw)
    return [p.strip() for p in parts if p and p.strip()]


BOT_TOKEN = env("BOT_TOKEN")
OPENROUTER_KEYS = env_list("OPENROUTER_KEYS")
OPENROUTER_MODEL = env("OPENROUTER_MODEL", "openai/gpt-4o-mini")
OPENROUTER_BASE = env("OPENROUTER_BASE", "https://openrouter.ai/api/v1")
HF_TOKENS = env_list("HF_TOKENS")
HF_CHAT_URL = env("HF_CHAT_URL")
HF_IMAGE_URL = env("HF_IMAGE_URL")
HF_ROUTER_URL = env("HF_ROUTER_URL")
HF_ROUTER_MODEL = env("HF_ROUTER_MODEL")
CF_ACCOUNT_ID = env("CF_ACCOUNT_ID")
CF_AI_TOKENS = env_list("CF_AI_TOKENS")
CF_AI_MODEL = env("CF_AI_MODEL")
TIKTOK_API_BASE = env("TIKTOK_API_BASE")
TIKTOK_API_KEY = env("TIKTOK_API_KEY")
FF_API_BASE = env("FF_API_BASE")
FF_API_KEY = env("FF_API_KEY")
FF_DEFAULT_REGION = env("FF_DEFAULT_REGION", "BD")
DUCKDUCKGO_API = env("DUCKDUCKGO_API", "https://api.duckduckgo.com/")
POLLINATIONS_IMAGE_BASE = env("POLLINATIONS_IMAGE_BASE", "https://image.pollinations.ai/prompt/")
RAPIDAPI_KEY = env("RAPIDAPI_KEY")
RAPIDAPI_HOST_YT = env("RAPIDAPI_HOST_YT")
RAPIDAPI_HOST_IG = env("RAPIDAPI_HOST_IG")
RAPIDAPI_HOST_TT_ADS = env("RAPIDAPI_HOST_TT_ADS")
RAPIDAPI_HOST_FB = env("RAPIDAPI_HOST_FB")
RAPIDAPI_HOST_BG = env("RAPIDAPI_HOST_BG")
APP_NAME = env("APP_NAME", "Noir Prime")
APP_URL = env("APP_URL", "https://render.com")
LOG_LEVEL = env("LOG_LEVEL", "INFO").upper()
REQUEST_TIMEOUT = env_int("REQUEST_TIMEOUT", 55)
MAX_HISTORY = env_int("MAX_HISTORY", 18)
MAX_TEXT = env_int("MAX_TEXT", 3800)
HARD_MODE = env_bool("HARD_MODE", True)
SYSTEM_PROMPT = env(
    "SYSTEM_PROMPT",
    (
        "You are a premium assistant. Speak in a natural, polished, smart, concise, and confident tone. "
        "Do not mention any internal services, providers, endpoints, API routing chains, model names, "
        "secret names, deployment details, or implementation details in user-facing text. "
        "You can assist with chat, rewrites, captions, coding help, explanations, search summaries, "
        "TikTok link analysis, Free Fire info, image prompts, fast answers, and stylish messages. "
        "Provide clean, useful, human-like, and premium quality responses."
    ),
)

if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN is missing. Set it in Environment Variables.")

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=LOG_LEVEL,
)
logger = logging.getLogger("noir_prime")


# ============================================================
# Data Models
# ============================================================
@dataclass
class ProviderResult:
    ok: bool
    text: str = ""
    data: Optional[Dict[str, Any]] = None
    error: str = ""


@dataclass
class IntentPack:
    name: str
    payload: Dict[str, Any] = field(default_factory=dict)


class RotatingPool:
    def __init__(self, items: Sequence[str]) -> None:
        self.items = [item.strip() for item in items if item and item.strip()]
        self.index = 0
        self.cooldown: Dict[str, float] = {}

    def ordered(self) -> List[str]:
        if not self.items:
            return []
        now = time()
        usable = [k for k in self.items if self.cooldown.get(k, 0) <= now]
        if not usable:
            usable = list(self.items)
        rotated = self.items[self.index :] + self.items[: self.index]
        self.index = (self.index + 1) % max(1, len(self.items))
        return [k for k in rotated if k in usable]

    def mark_bad(self, item: str, seconds: int = 120) -> None:
        self.cooldown[item] = time() + seconds


openrouter_pool = RotatingPool(OPENROUTER_KEYS)
hf_pool = RotatingPool(HF_TOKENS)
cf_pool = RotatingPool(CF_AI_TOKENS)

user_histories: Dict[int, Deque[Dict[str, str]]] = defaultdict(lambda: deque(maxlen=MAX_HISTORY))
user_modes: Dict[int, str] = defaultdict(lambda: "auto")
user_styles: Dict[int, str] = defaultdict(lambda: "premium")


# ============================================================
# Regex & Intent Keywords
# ============================================================
TIKTOK_RE = re.compile(r"https?://(?:www\.)?(?:m\.|vm\.)?tiktok\.com/\S+", re.I)
YT_VIDEO_RE = re.compile(r"https?://(?:www\.)?(?:youtube\.com/(?:watch\?v=|shorts/)|youtu\.be/)[\w-]+", re.I)
URL_RE = re.compile(r"https?://\S+", re.I)
UID_RE = re.compile(r"\b\d{7,14}\b")
YT_CHANNEL_ID_RE = re.compile(r"\bUC[a-zA-Z0-9_-]{20,30}\b")

SEARCH_TRIGGERS = {"search", "find", "lookup", "look up", "discover", "show info", "search about"}
IMAGE_TRIGGERS = {"image", "img", "photo", "picture", "generate image", "draw", "art"}
FF_TRIGGERS = {"free fire", "ff", "uid", "player info", "player", "freefire"}
TIKTOK_TRIGGERS = {"tiktok", "tik tok", "video link", "no watermark", "download tiktok"}
CHAT_STYLE_PRESETS = {
    "premium": "Response must be polished, premium, confident, and stylish.",
    "concise": "Response must be short, direct, and low-fluff.",
    "friendly": "Response must be warm, friendly, and accessible.",
    "pro": "Response must be professional, structured, and sharp.",
}
REGION_CODES = {
    "bd": "BD", "sg": "SG", "ind": "IND", "br": "BR", "id": "ID",
    "me": "ME", "pk": "PK", "ru": "RU", "th": "TH", "vn": "VN", "us": "US",
}


class Intent:
    HELP = "help"
    CHAT = "chat"
    CLEAR = "clear"
    TIKTOK = "tiktok"
    YOUTUBE = "youtube"
    FREE_FIRE = "free_fire"
    IMAGE = "image"
    SEARCH = "search"
    YT_CHANNEL = "yt_channel"
    INSTAGRAM = "instagram"
    TIKTOK_ADS = "tiktok_ads"
    FACEBOOK = "facebook"
    BG_REMOVE = "bg_remove"
    STYLE = "style"
    MODE = "mode"


# ============================================================
# UI Helpers
# ============================================================
def esc(text: Any) -> str:
    return html.escape(str(text or ""))


def safe(obj: Any, limit: int = 300) -> str:
    text = obj if isinstance(obj, str) else json.dumps(obj, ensure_ascii=False)
    text = text.replace("\n", " ").strip()
    return text[:limit] + ("…" if len(text) > limit else "")


def clamp_text(text: str, limit: int = MAX_TEXT) -> str:
    text = (text or "").strip()
    return text[:limit] + ("…" if len(text) > limit else "")


def chunks(text: str, size: int = MAX_TEXT) -> List[str]:
    text = text or ""
    if len(text) <= size:
        return [text]

    out: List[str] = []
    current = ""
    for part in text.split("\n"):
        part_line = part + "\n"
        if len(current) + len(part_line) > size:
            if current:
                out.append(current.rstrip())
            current = part_line
        else:
            current += part_line
    if current.strip():
        out.append(current.rstrip())
    return out or [text[:size]]


def premium_keyboard() -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton("✨ Smart Chat"), KeyboardButton("🔎 Search")],
        [KeyboardButton("🖼 Image"), KeyboardButton("🎵 TikTok"), KeyboardButton("▶️ YouTube")],
        [KeyboardButton("🎮 Free Fire"), KeyboardButton("🧹 Clear")],
    ]
    return ReplyKeyboardMarkup(rows, resize_keyboard=True, input_field_placeholder="Type anything…")


def premium_panel() -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton("✨ Auto Mode", callback_data="mode:auto"), InlineKeyboardButton("🧠 Pro Style", callback_data="style:pro")],
        [InlineKeyboardButton("⚡ Concise", callback_data="style:concise"), InlineKeyboardButton("💬 Friendly", callback_data="style:friendly")],
        [InlineKeyboardButton("🎨 Image Menu", callback_data="help:image"), InlineKeyboardButton("🔎 Search Menu", callback_data="help:search")],
    ]
    return InlineKeyboardMarkup(rows)


def brand_header(title: str, emoji: str = "✦") -> str:
    return f"<b>{emoji} {esc(title)}</b>"


def premium_block(title: str, body: str, emoji: str = "✦") -> str:
    return f"{brand_header(title, emoji)}\n{body.strip()}"


async def send_html(update: Update, text: str, reply_markup=None) -> None:
    if not update.effective_chat:
        return

    for i, part in enumerate(chunks(text)):
        try:
            await update.effective_chat.send_message(
                part,
                parse_mode="HTML",
                disable_web_page_preview=False,
                reply_markup=reply_markup if i == 0 else None,
            )
        except BadRequest:
            await update.effective_chat.send_message(
                html.unescape(re.sub(r"<[^>]+>", "", part)),
                disable_web_page_preview=False,
                reply_markup=reply_markup if i == 0 else None,
            )


class TypingLoop:
    def __init__(
        self,
        chat_id: int,
        application: Application,
        action: str = ChatAction.TYPING,
        interval: float = 4.0,
    ) -> None:
        self.chat_id = chat_id
        self.application = application
        self.action = action
        self.interval = interval
        self.task: Optional[asyncio.Task] = None
        self.running = False

    async def _run(self) -> None:
        while self.running:
            try:
                await self.application.bot.send_chat_action(chat_id=self.chat_id, action=self.action)
            except Exception:
                pass
            await asyncio.sleep(self.interval)

    async def __aenter__(self) -> "TypingLoop":
        self.running = True
        self.task = asyncio.create_task(self._run())
        return self

    async def __aexit__(self, exc_type, exc, tb) -> None:
        self.running = False
        if self.task:
            self.task.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await self.task


# ============================================================
# HTTP Helpers
# ============================================================
async def get_session(application: Application) -> aiohttp.ClientSession:
    session = application.bot_data.get("http_session")
    if session and not session.closed:
        return session

    timeout = aiohttp.ClientTimeout(total=REQUEST_TIMEOUT)
    connector = aiohttp.TCPConnector(limit=80)
    session = aiohttp.ClientSession(timeout=timeout, connector=connector)
    application.bot_data["http_session"] = session
    return session


async def close_session(application: Application) -> None:
    session = application.bot_data.get("http_session")
    if session and not session.closed:
        await session.close()


async def http_json(
    session: aiohttp.ClientSession,
    method: str,
    url: str,
    *,
    headers: Optional[Dict[str, str]] = None,
    params: Optional[Dict[str, Any]] = None,
    json_data: Optional[Dict[str, Any]] = None,
    data: Any = None,
) -> Tuple[int, Any]:
    async with session.request(method, url, headers=headers, params=params, json=json_data, data=data) as resp:
        raw = await resp.text()
        content_type = resp.headers.get("Content-Type", "")

        if "application/json" in content_type:
            try:
                return resp.status, json.loads(raw)
            except Exception:
                return resp.status, {"raw": raw}

        try:
            return resp.status, json.loads(raw)
        except Exception:
            return resp.status, {"raw": raw}


async def http_bytes(
    session: aiohttp.ClientSession,
    method: str,
    url: str,
    *,
    headers: Optional[Dict[str, str]] = None,
    params: Optional[Dict[str, Any]] = None,
    json_data: Optional[Dict[str, Any]] = None,
    data: Any = None,
) -> Tuple[int, bytes, str]:
    async with session.request(method, url, headers=headers, params=params, json=json_data, data=data) as resp:
        blob = await resp.read()
        return resp.status, blob, resp.headers.get("Content-Type", "")


# ============================================================
# Intent Engine
# ============================================================
def extract_region(text: str) -> str:
    low = f" {text.lower()} "
    for key, value in REGION_CODES.items():
        if f" {key} " in low:
            return value
    if " bangladesh " in low or " bd " in low:
        return "BD"
    return FF_DEFAULT_REGION


def normalize_ui_text(text: str) -> str:
    text = text.strip()
    aliases = {
        "✨ smart chat": "chat",
        "🔎 search": "search",
        "🖼 image": "image",
        "🎵 tiktok": "tiktok",
        "▶️ youtube": "youtube",
        "🎮 free fire": "ff",
        "🧹 clear": "clear",
    }
    return aliases.get(text.lower(), text)


def detect_intent(text: str) -> IntentPack:
    raw = normalize_ui_text((text or "").strip())
    low = raw.lower()

    if not raw:
        return IntentPack(Intent.CHAT)

    if low in {"/start", "start", "help", "/help", "menu", "hi", "hello"}:
        return IntentPack(Intent.HELP)
    if low in {"/clear", "clear", "reset", "🧹 clear"}:
        return IntentPack(Intent.CLEAR)

    if low.startswith("style "):
        style = low.split(" ", 1)[1].strip()
        if style in CHAT_STYLE_PRESETS:
            return IntentPack(Intent.STYLE, {"style": style})

    if low.startswith("mode "):
        mode = low.split(" ", 1)[1].strip()
        return IntentPack(Intent.MODE, {"mode": mode})

    match_tiktok = TIKTOK_RE.search(raw)
    if match_tiktok:
        return IntentPack(Intent.TIKTOK, {"url": match_tiktok.group(0)})

    match_youtube = YT_VIDEO_RE.search(raw)
    if match_youtube:
        return IntentPack(Intent.YOUTUBE, {"url": match_youtube.group(0)})

    if any(trigger in low for trigger in TIKTOK_TRIGGERS):
        maybe_url = URL_RE.search(raw)
        return IntentPack(Intent.TIKTOK, {"url": maybe_url.group(0) if maybe_url else "", "query": raw})

    if any(trigger in low for trigger in IMAGE_TRIGGERS):
        prompt = re.sub(r"(?i)^(image|img|photo|picture|draw|art)\s*[:\-]?\s*", "", raw).strip()
        return IntentPack(Intent.IMAGE, {"prompt": prompt or raw})

    if any(trigger in low for trigger in SEARCH_TRIGGERS):
        query = re.sub(r"(?i)^(search|find|lookup|look up)\s*[:\-]?\s*", "", raw).strip()
        return IntentPack(Intent.SEARCH, {"query": query or raw})

    if any(trigger in low for trigger in FF_TRIGGERS):
        uid_match = UID_RE.search(raw)
        return IntentPack(Intent.FREE_FIRE, {"uid": uid_match.group(0) if uid_match else "", "region": extract_region(raw)})

    if "channel/about?id=" in low or YT_CHANNEL_ID_RE.search(raw):
        channel_id = YT_CHANNEL_ID_RE.search(raw)
        return IntentPack(Intent.YT_CHANNEL, {"channel_id": channel_id.group(0) if channel_id else raw.strip()})

    if "instagram" in low and ("iid" in low or UID_RE.search(raw)):
        iid = UID_RE.search(raw)
        return IntentPack(Intent.INSTAGRAM, {"iid": iid.group(0) if iid else ""})

    if "tiktok ads" in low or ("ads" in low and "tiktok" in low):
        return IntentPack(Intent.TIKTOK_ADS)

    if "facebook" in low and ("page" in low or "search" in low):
        query = raw.split("facebook", 1)[-1].strip()
        return IntentPack(Intent.FACEBOOK, {"query": query or raw})

    if "remove background" in low or "background remove" in low or "bg remove" in low:
        maybe_url = URL_RE.search(raw)
        return IntentPack(Intent.BG_REMOVE, {"url": maybe_url.group(0) if maybe_url else ""})

    return IntentPack(Intent.CHAT)


# ============================================================
# History Helpers
# ============================================================
def add_history(user_id: int, role: str, content: str) -> None:
    user_histories[user_id].append({"role": role, "content": clamp_text(content, 2500)})


def clear_history(user_id: int) -> None:
    user_histories[user_id].clear()


def build_messages(user_id: int, prompt: str) -> List[Dict[str, str]]:
    style = user_styles[user_id]
    style_note = CHAT_STYLE_PRESETS.get(style, CHAT_STYLE_PRESETS["premium"])
    messages: List[Dict[str, str]] = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "system", "content": style_note},
    ]
    messages.extend(list(user_histories[user_id]))
    messages.append({"role": "user", "content": prompt})
    return messages


# ============================================================
# AI Provider Chain
# ============================================================
async def call_openrouter(session: aiohttp.ClientSession, messages: List[Dict[str, str]]) -> ProviderResult:
    if not OPENROUTER_KEYS:
        return ProviderResult(ok=False, error="No API key found.")

    url = f"{OPENROUTER_BASE.rstrip('/')}/chat/completions"
    payload = {"model": OPENROUTER_MODEL, "messages": messages, "temperature": 0.7}
    headers_base = {
        "Content-Type": "application/json",
        "HTTP-Referer": APP_URL,
        "X-Title": APP_NAME,
    }
    errors: List[str] = []

    for key in openrouter_pool.ordered():
        try:
            status, data = await http_json(
                session,
                "POST",
                url,
                headers={**headers_base, "Authorization": f"Bearer {key}"},
                json_data=payload,
            )
            if status < 400 and isinstance(data, dict) and data.get("choices"):
                content = data["choices"][0].get("message", {}).get("content", "")
                if isinstance(content, list):
                    content = "\n".join(item.get("text", "") for item in content if isinstance(item, dict))
                if content:
                    return ProviderResult(ok=True, text=clamp_text(str(content), 7000), data=data)
            errors.append(f"{status}: {safe(data, 160)}")
            if status in {401, 402, 403, 429, 500, 502, 503}:
                openrouter_pool.mark_bad(key, 180)
        except Exception as exc:
            errors.append(str(exc))
            openrouter_pool.mark_bad(key, 120)

    return ProviderResult(ok=False, error=" | ".join(errors[:3]))


async def call_hf_router(session: aiohttp.ClientSession, messages: List[Dict[str, str]]) -> ProviderResult:
    if not HF_TOKENS or not HF_ROUTER_URL or not HF_ROUTER_MODEL:
        return ProviderResult(ok=False, error="Hugging Face router not configured.")

    payload = {
        "model": HF_ROUTER_MODEL,
        "messages": messages,
        "temperature": 0.7,
        "max_tokens": 700,
    }
    errors: List[str] = []

    for token in hf_pool.ordered():
        try:
            status, data = await http_json(
                session,
                "POST",
                HF_ROUTER_URL,
                headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
                json_data=payload,
            )
            if status < 400 and isinstance(data, dict) and data.get("choices"):
                content = data["choices"][0].get("message", {}).get("content", "")
                if content:
                    return ProviderResult(ok=True, text=clamp_text(str(content), 7000), data=data)
            errors.append(f"{status}: {safe(data, 160)}")
            if status in {401, 402, 403, 429, 500, 502, 503}:
                hf_pool.mark_bad(token, 180)
        except Exception as exc:
            errors.append(str(exc))
            hf_pool.mark_bad(token, 120)

    return ProviderResult(ok=False, error=" | ".join(errors[:3]))


async def call_hf_model(session: aiohttp.ClientSession, prompt: str) -> ProviderResult:
    if not HF_TOKENS or not HF_CHAT_URL:
        return ProviderResult(ok=False, error="Hugging Face model not configured.")

    payloads = [
        {"inputs": prompt, "parameters": {"max_new_tokens": 700, "return_full_text": False}},
        {"messages": [{"role": "user", "content": prompt}], "max_new_tokens": 700},
    ]
    errors: List[str] = []

    for token in hf_pool.ordered():
        headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
        for payload in payloads:
            try:
                status, data = await http_json(session, "POST", HF_CHAT_URL, headers=headers, json_data=payload)
                if status < 400:
                    if isinstance(data, list) and data:
                        first = data[0]
                        text = first.get("generated_text") or first.get("summary_text") or first.get("text")
                        if text:
                            return ProviderResult(ok=True, text=clamp_text(str(text), 7000), data={"items": data})
                    if isinstance(data, dict):
                        for key in ("generated_text", "summary_text", "text", "response"):
                            if data.get(key):
                                return ProviderResult(ok=True, text=clamp_text(str(data[key]), 7000), data=data)
                errors.append(f"{status}: {safe(data, 160)}")
                if status in {401, 402, 403, 429, 500, 502, 503}:
                    hf_pool.mark_bad(token, 180)
            except Exception as exc:
                errors.append(str(exc))
                hf_pool.mark_bad(token, 120)

    return ProviderResult(ok=False, error=" | ".join(errors[:3]))


async def call_cloudflare(session: aiohttp.ClientSession, messages: List[Dict[str, str]]) -> ProviderResult:
    if not CF_ACCOUNT_ID or not CF_AI_TOKENS or not CF_AI_MODEL:
        return ProviderResult(ok=False, error="Cloudflare AI not configured.")

    url = f"https://api.cloudflare.com/client/v4/accounts/{CF_ACCOUNT_ID}/ai/run/{CF_AI_MODEL}"
    prompt = "\n".join(f"{m['role'].upper()}: {m['content']}" for m in messages[-10:])
    payload = {"messages": messages, "prompt": prompt}
    errors: List[str] = []

    for token in cf_pool.ordered():
        try:
            status, data = await http_json(
                session,
                "POST",
                url,
                headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
                json_data=payload,
            )
            if status < 400 and isinstance(data, dict):
                result = data.get("result") or {}
                text = result.get("response") or result.get("output") or result.get("text")
                if isinstance(text, list):
                    text = "\n".join(str(x) for x in text)
                if text:
                    return ProviderResult(ok=True, text=clamp_text(str(text), 7000), data=data)
            errors.append(f"{status}: {safe(data, 160)}")
            if status in {401, 403, 429, 500, 502, 503}:
                cf_pool.mark_bad(token, 180)
        except Exception as exc:
            errors.append(str(exc))
            cf_pool.mark_bad(token, 120)

    return ProviderResult(ok=False, error=" | ".join(errors[:3]))


async def smart_chat(session: aiohttp.ClientSession, user_id: int, prompt: str) -> ProviderResult:
    messages = build_messages(user_id, prompt)
    providers = [
        lambda: call_openrouter(session, messages),
        lambda: call_hf_router(session, messages),
        lambda: call_hf_model(session, prompt),
        lambda: call_cloudflare(session, messages),
    ]
    last_error = ""
    for provider in providers:
        result = await provider()
        if result.ok and result.text.strip():
            return result
        last_error = result.error or last_error
    return ProviderResult(ok=False, error=last_error or "Service temporarily unavailable.")


# ============================================================
# Remote Skills
# ============================================================
async def fetch_tiktok_info(session: aiohttp.ClientSession, url: str) -> ProviderResult:
    if not url or not TIKTOK_API_BASE:
        return ProviderResult(ok=False, error="Missing link or API base configuration.")
    status, data = await http_json(session, "GET", TIKTOK_API_BASE, params={"key": TIKTOK_API_KEY, "url": url})
    if status >= 400:
        return ProviderResult(ok=False, error=f"{status}: {safe(data)}")
    return ProviderResult(ok=True, data=data)


async def fetch_free_fire(session: aiohttp.ClientSession, uid: str, region: str) -> ProviderResult:
    if not uid or not FF_API_BASE or not FF_API_KEY:
        return ProviderResult(ok=False, error="Missing UID or API configuration.")
    params = {"apikey": FF_API_KEY, "uid": uid, "region": region or FF_DEFAULT_REGION}
    status, data = await http_json(session, "GET", FF_API_BASE, params=params)
    if status >= 400:
        return ProviderResult(ok=False, error=f"{status}: {safe(data)}")
    return ProviderResult(ok=True, data=data)


async def duckduckgo_search(session: aiohttp.ClientSession, query: str) -> ProviderResult:
    if not query:
        return ProviderResult(ok=False, error="Missing search query.")
    params = {"q": query, "format": "json", "no_html": "1", "skip_disambig": "1"}
    status, data = await http_json(session, "GET", DUCKDUCKGO_API, params=params)
    if status >= 400:
        return ProviderResult(ok=False, error=f"{status}: {safe(data)}")
    return ProviderResult(ok=True, data=data)


async def generate_image_pollinations(session: aiohttp.ClientSession, prompt: str) -> ProviderResult:
    if not prompt or not POLLINATIONS_IMAGE_BASE:
        return ProviderResult(ok=False, error="Missing prompt or image base configuration.")
    url = f"{POLLINATIONS_IMAGE_BASE.rstrip('/')}/{quote(prompt)}?model=flux"
    status, blob, content_type = await http_bytes(session, "GET", url)
    if status >= 400 or not blob:
        return ProviderResult(ok=False, error=f"{status}: Image generation failed.")
    return ProviderResult(ok=True, data={"bytes": blob, "content_type": content_type, "url": url})


async def rapidapi_get(session: aiohttp.ClientSession, host: str, path_or_url: str) -> ProviderResult:
    if not RAPIDAPI_KEY or not host:
        return ProviderResult(ok=False, error="RapidAPI not configured.")
    url = path_or_url if path_or_url.startswith(("http://", "https://")) else f"https://{host}{path_or_url}"
    headers = {
        "Content-Type": "application/json",
        "x-rapidapi-host": host,
        "x-rapidapi-key": RAPIDAPI_KEY,
    }
    status, data = await http_json(session, "GET", url, headers=headers)
    if status >= 400:
        return ProviderResult(ok=False, error=f"{status}: {safe(data)}")
    return ProviderResult(ok=True, data=data)


async def rapidapi_post_form(session: aiohttp.ClientSession, host: str, path_or_url: str, form_data: Dict[str, Any]) -> ProviderResult:
    if not RAPIDAPI_KEY or not host:
        return ProviderResult(ok=False, error="RapidAPI not configured.")
    url = path_or_url if path_or_url.startswith(("http://", "https://")) else f"https://{host}{path_or_url}"
    headers = {
        "Content-Type": "application/x-www-form-urlencoded",
        "x-rapidapi-host": host,
        "x-rapidapi-key": RAPIDAPI_KEY,
    }
    status, data = await http_json(session, "POST", url, headers=headers, data=form_data)
    if status >= 400:
        return ProviderResult(ok=False, error=f"{status}: {safe(data)}")
    return ProviderResult(ok=True, data=data)


# ============================================================
# Formatters
# ============================================================
def format_tiktok(data: Dict[str, Any]) -> str:
    title = data.get("title") or data.get("desc") or data.get("video_title") or "TikTok Result"
    author = data.get("author") or data.get("username") or data.get("owner") or "Unknown"
    duration = data.get("duration") or data.get("video_duration") or "—"
    stats = data.get("stats") or {}
    likes = stats.get("likes") or data.get("like_count") or data.get("likes") or "—"
    comments = stats.get("comments") or data.get("comment_count") or data.get("comments") or "—"
    shares = stats.get("shares") or data.get("share_count") or data.get("shares") or "—"
    download = data.get("download") or data.get("download_url") or data.get("video") or data.get("nowm") or data.get("url") or ""
    body = (
        f"<b>Title:</b> {esc(title)}\n"
        f"<b>Author:</b> {esc(author)}\n"
        f"<b>Duration:</b> {esc(duration)}\n"
        f"<b>Likes:</b> {esc(likes)}\n"
        f"<b>Comments:</b> {esc(comments)}\n"
        f"<b>Shares:</b> {esc(shares)}"
    )
    if download:
        body += f"\n<b>Link:</b> {esc(download)}"
    return premium_block("TikTok", body, "🎵")


def deep_find(data: Any, keys: Iterable[str]) -> Optional[Any]:
    keyset = set(keys)
    if isinstance(data, dict):
        for key, value in data.items():
            if key in keyset:
                return value
            found = deep_find(value, keys)
            if found is not None:
                return found
    elif isinstance(data, list):
        for item in data:
            found = deep_find(item, keys)
            if found is not None:
                return found
    return None


def format_ff(data: Dict[str, Any], uid: str, region: str) -> str:
    payload = data.get("data") if isinstance(data, dict) and data.get("data") else data
    name = deep_find(payload, {"nickname", "name", "player_name", "username"}) or "Unknown"
    level = deep_find(payload, {"level", "account_level"}) or "—"
    likes = deep_find(payload, {"likes", "liked"}) or "—"
    rank = deep_find(payload, {"rank", "current_rank", "br_rank"}) or "—"
    clan = deep_find(payload, {"guild_name", "clan", "guild"}) or "—"
    server = deep_find(payload, {"region", "server"}) or region
    body = (
        f"<b>UID:</b> {esc(uid)}\n"
        f"<b>Name:</b> {esc(name)}\n"
        f"<b>Region:</b> {esc(server)}\n"
        f"<b>Level:</b> {esc(level)}\n"
        f"<b>Likes:</b> {esc(likes)}\n"
        f"<b>Rank:</b> {esc(rank)}\n"
        f"<b>Guild:</b> {esc(clan)}"
    )
    return premium_block("Free Fire Profile", body, "🎮")


def format_search_summary(query: str, raw: Dict[str, Any], answer: str) -> str:
    abstract = raw.get("AbstractText") or raw.get("Answer") or raw.get("Definition") or ""
    related = raw.get("RelatedTopics") or []
    related_lines: List[str] = []
    for item in related[:5]:
        if isinstance(item, dict):
            text = item.get("Text") or ""
            if text:
                related_lines.append(f"• {esc(text)}")
        if len(related_lines) >= 3:
            break
    body = f"<b>Query:</b> {esc(query)}\n\n{esc(answer)}"
    if abstract:
        body += f"\n\n<b>Quick Note:</b> {esc(abstract)}"
    if related_lines:
        body += "\n\n<b>More Information:</b>\n" + "\n".join(related_lines)
    return premium_block("Search Result", body, "🔎")


def format_channel(data: Dict[str, Any], channel_id: str) -> str:
    title = data.get("title") or data.get("name") or data.get("author") or "Channel"
    sub = data.get("subscriberCountText") or data.get("subscriber_count") or data.get("subscribers") or "—"
    videos = data.get("videosCountText") or data.get("videos_count") or data.get("videos") or "—"
    views = data.get("viewCountText") or data.get("views") or "—"
    country = data.get("country") or "—"
    body = (
        f"<b>Channel:</b> {esc(title)}\n"
        f"<b>ID:</b> {esc(channel_id)}\n"
        f"<b>Subscribers:</b> {esc(sub)}\n"
        f"<b>Videos:</b> {esc(videos)}\n"
        f"<b>Views:</b> {esc(views)}\n"
        f"<b>Country:</b> {esc(country)}"
    )
    return premium_block("Channel Info", body, "📺")


def format_instagram(data: Dict[str, Any]) -> str:
    items = data.get("items") or data.get("feed") or data.get("data") or []
    count = len(items) if isinstance(items, list) else "—"
    first = items[0] if isinstance(items, list) and items else {}
    caption = first.get("caption") if isinstance(first, dict) else ""
    body = f"<b>Posts Found:</b> {esc(count)}"
    if caption:
        body += f"\n<b>Latest Caption:</b> {esc(str(caption)[:600])}"
    return premium_block("Instagram Feed", body, "📸")


def format_tiktok_ads(data: Dict[str, Any]) -> str:
    items = data.get("data") or data.get("items") or data.get("ads") or []
    lines: List[str] = []
    if isinstance(items, list):
        for item in items[:5]:
            if isinstance(item, dict):
                title = item.get("title") or item.get("ad_text") or item.get("name") or "Ad"
                imp = item.get("impression") or item.get("impressions") or item.get("reach") or "—"
                lines.append(f"• {esc(title)} — {esc(imp)}")
    body = "\n".join(lines) if lines else esc(safe(data, 900))
    return premium_block("TikTok Ads", body, "📈")


def format_facebook(data: Dict[str, Any]) -> str:
    items = data.get("data") or data.get("results") or []
    lines: List[str] = []
    if isinstance(items, list):
        for item in items[:5]:
            if isinstance(item, dict):
                name = item.get("name") or item.get("title") or "Page"
                likes = item.get("likes") or item.get("followers") or "—"
                lines.append(f"• {esc(name)} — {esc(likes)}")
    body = "\n".join(lines) if lines else esc(safe(data, 900))
    return premium_block("Facebook Search", body, "📘")


# ============================================================
# Response Generation
# ============================================================
async def answer_chat(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str) -> None:
    if not update.effective_chat or not update.effective_user:
        return
    session = await get_session(context.application)
    user_id = update.effective_user.id

    async with TypingLoop(update.effective_chat.id, context.application):
        result = await smart_chat(session, user_id, text)

    if result.ok:
        add_history(user_id, "user", text)
        add_history(user_id, "assistant", result.text)
        await send_html(update, premium_block("Reply", esc(result.text), "✨"), reply_markup=premium_panel())
    else:
        await send_html(
            update,
            premium_block("Unavailable", "Unable to retrieve response at this moment. Please try again later.", "⚠️"),
            reply_markup=premium_panel(),
        )


async def answer_search(update: Update, context: ContextTypes.DEFAULT_TYPE, query: str) -> None:
    if not update.effective_chat or not update.effective_user:
        return
    session = await get_session(context.application)

    async with TypingLoop(update.effective_chat.id, context.application):
        raw_result = await duckduckgo_search(session, query)
        if not raw_result.ok:
            await send_html(update, premium_block("Search", "No results found or service unavailable.", "🔎"))
            return

        raw = raw_result.data or {}
        summary_prompt = (
            f"Provide a short, smart, and accurate summary for the user based on this search data. Query: {query}\n"
            f"Raw: {json.dumps(raw, ensure_ascii=False)[:3500]}"
        )
        ai = await smart_chat(session, update.effective_user.id, summary_prompt)
        answer = ai.text if ai.ok else (raw.get("AbstractText") or raw.get("Answer") or "Brief information could not be found.")

    await send_html(update, format_search_summary(query, raw, answer), reply_markup=premium_panel())


async def answer_image(update: Update, context: ContextTypes.DEFAULT_TYPE, prompt: str) -> None:
    if not update.effective_chat:
        return
    session = await get_session(context.application)
    prompt = re.sub(r"(?i)^(image|img|photo|picture|draw|art)\s*[:\-]?\s*", "", prompt).strip()
    if not prompt:
        prompt = "cinematic premium portrait with dramatic lighting"

    async with TypingLoop(update.effective_chat.id, context.application, ChatAction.UPLOAD_PHOTO):
        result = await generate_image_pollinations(session, prompt)

    if not result.ok:
        await send_html(update, premium_block("Image", "Failed to generate image. Try a different prompt.", "🖼"))
        return

    blob = result.data.get("bytes") if result.data else None
    if not blob:
        await send_html(update, premium_block("Image", "Image not found.", "🖼"))
        return

    bio = io.BytesIO(blob)
    bio.name = "noir_prime_image.jpg"
    caption = premium_block("Image Ready", f"<b>Prompt:</b> {esc(prompt)}", "🖼")
    await update.effective_chat.send_photo(photo=bio, caption=caption, parse_mode="HTML", reply_markup=premium_panel())


async def answer_tiktok(update: Update, context: ContextTypes.DEFAULT_TYPE, url: str) -> None:
    if not update.effective_chat:
        return
    if not url:
        await send_html(update, premium_block("TikTok", "Please send a valid TikTok link.", "🎵"))
        return
    session = await get_session(context.application)
    async with TypingLoop(update.effective_chat.id, context.application):
        result = await fetch_tiktok_info(session, url)
    if not result.ok:
        await send_html(update, premium_block("TikTok", "Failed to fetch information from the link.", "🎵"))
        return
    await send_html(update, format_tiktok(result.data or {}), reply_markup=premium_panel())


async def answer_youtube(update: Update, context: ContextTypes.DEFAULT_TYPE, url: str) -> None:
    if not update.effective_chat:
        return
    if not url:
        await send_html(update, premium_block("YouTube", "Please send a valid YouTube link.", "▶️"))
        return

    async with TypingLoop(update.effective_chat.id, context.application):
        try:
            ydl_opts = {'format': 'best', 'quiet': True, 'noplaylist': True}
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = await asyncio.to_thread(ydl.extract_info, url, download=False)
                title = info.get('title', 'Unknown Title')
                duration = info.get('duration_string', '—')
                uploader = info.get('uploader', 'Unknown')
                view_count = info.get('view_count', '—')
                video_url = info.get('url', '')

                body = (
                    f"<b>Title:</b> {esc(title)}\n"
                    f"<b>Channel:</b> {esc(uploader)}\n"
                    f"<b>Duration:</b> {esc(duration)}\n"
                    f"<b>Views:</b> {esc(view_count)}\n\n"
                    f"<b>Download:</b> <a href='{video_url}'>Click Here To Download</a>"
                )
                await send_html(update, premium_block("YouTube Downloader", body, "▶️"), reply_markup=premium_panel())
        except Exception as e:
            await send_html(update, premium_block("YouTube Error", f"Failed to process video: {str(e)[:100]}", "❌"))


async def answer_ff(update: Update, context: ContextTypes.DEFAULT_TYPE, uid: str, region: str) -> None:
    if not update.effective_chat:
        return
    if not uid:
        await send_html(update, premium_block("Free Fire", "Please send a UID. Example: ff 12345678 bd", "🎮"))
        return
    session = await get_session(context.application)
    async with TypingLoop(update.effective_chat.id, context.application):
        result = await fetch_free_fire(session, uid, region)
    if not result.ok:
        await send_html(update, premium_block("Free Fire", "Unable to fetch info for this UID.", "🎮"))
        return
    await send_html(update, format_ff(result.data or {}, uid, region), reply_markup=premium_panel())


async def answer_yt_channel(update: Update, context: ContextTypes.DEFAULT_TYPE, channel_id: str) -> None:
    if not update.effective_chat:
        return
    if not channel_id:
        await send_html(update, premium_block("Channel", "Please provide a Channel ID.", "📺"))
        return
    session = await get_session(context.application)
    path = f"/channel/about?id={quote_plus(channel_id)}"
    async with TypingLoop(update.effective_chat.id, context.application):
        result = await rapidapi_get(session, RAPIDAPI_HOST_YT, path)
    if not result.ok:
        await send_html(update, premium_block("Channel", "Failed to fetch channel info.", "📺"))
        return
    await send_html(update, format_channel(result.data or {}, channel_id), reply_markup=premium_panel())


async def answer_instagram(update: Update, context: ContextTypes.DEFAULT_TYPE, iid: str) -> None:
    if not update.effective_chat:
        return
    if not iid:
        await send_html(update, premium_block("Instagram", "Please provide a User IID.", "📸"))
        return
    session = await get_session(context.application)
    path = f"/user/feed/?user-iid={quote_plus(iid)}"
    async with TypingLoop(update.effective_chat.id, context.application):
        result = await rapidapi_get(session, RAPIDAPI_HOST_IG, path)
    if not result.ok:
        await send_html(update, premium_block("Instagram", "Failed to load feed.", "📸"))
        return
    await send_html(update, format_instagram(result.data or {}), reply_markup=premium_panel())


async def answer_tiktok_ads(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_chat:
        return
    session = await get_session(context.application)
    path = "/ads/top/ads?page=1&limit=20&period=30&country_code=US%2CDE&ad_language=en%2Cde&order_by=impression"
    async with TypingLoop(update.effective_chat.id, context.application):
        result = await rapidapi_get(session, RAPIDAPI_HOST_TT_ADS, path)
    if not result.ok:
        await send_html(update, premium_block("TikTok Ads", "Failed to fetch ad data.", "📈"))
        return
    await send_html(update, format_tiktok_ads(result.data or {}), reply_markup=premium_panel())


async def answer_facebook(update: Update, context: ContextTypes.DEFAULT_TYPE, query: str) -> None:
    if not update.effective_chat:
        return
    if not query:
        await send_html(update, premium_block("Facebook", "Please provide a search query.", "📘"))
        return
    session = await get_session(context.application)
    path = f"/search/pages?query={quote_plus(query)}"
    async with TypingLoop(update.effective_chat.id, context.application):
        result = await rapidapi_get(session, RAPIDAPI_HOST_FB, path)
    if not result.ok:
        await send_html(update, premium_block("Facebook", "Failed to load search results.", "📘"))
        return
    await send_html(update, format_facebook(result.data or {}), reply_markup=premium_panel())


async def answer_bg_remove(update: Update, context: ContextTypes.DEFAULT_TYPE, url: str) -> None:
    if not update.effective_chat:
        return
    if not url:
        await send_html(update, premium_block("Background Remove", "Please provide an Image URL.", "🪄"))
        return
    session = await get_session(context.application)
    form_data = {"image": "", "url": url, "image-bg": "", "url-bg": ""}
    async with TypingLoop(update.effective_chat.id, context.application):
        result = await rapidapi_post_form(session, RAPIDAPI_HOST_BG, "/v1/results?mode=fg-image", form_data)
    if not result.ok:
        await send_html(update, premium_block("Background Remove", "Failed to process image.", "🪄"))
        return
    data = result.data or {}
    output_url = deep_find(data, {"url", "result", "fg_image_url", "image_url"})
    body = "<b>Status:</b> Done"
    if output_url:
        body += f"\n<b>Output URL:</b> {esc(output_url)}"
    else:
        body += f"\n{esc(safe(data, 1000))}"
    await send_html(update, premium_block("Background Remove", body, "🪄"), reply_markup=premium_panel())


# ============================================================
# Commands & Callbacks
# ============================================================
START_TEXT = (
    f"{brand_header(APP_NAME, '🌌')}\n"
    f"<i>Premium Smart Assistant</i>\n\n"
    f"<b>Features Included:</b>\n"
    f"• Natural smart chat\n"
    f"• Search and quick summary\n"
    f"• Image generation\n"
    f"• TikTok link info\n"
    f"• YouTube Download\n"
    f"• Free Fire profile info\n"
    f"• Social/query tools\n\n"
    f"<b>Examples:</b>\n"
    f"• who is nikola tesla\n"
    f"• search dubai visa from bangladesh\n"
    f"• image neon tiger in rain\n"
    f"• ff 12345678 bd\n"
    f"• https://www.tiktok.com/...\n"
    f"• https://www.youtube.com/watch?v=...\n\n"
    f"<b>Quick Styles:</b>\n"
    f"• style premium\n"
    f"• style concise\n"
    f"• style friendly\n"
    f"• style pro"
)


async def start_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await send_html(update, START_TEXT, reply_markup=premium_keyboard())
    await send_html(update, premium_block("Control Panel", "Tap buttons or type naturally.", "⚙️"), reply_markup=premium_panel())


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await start_cmd(update, context)


async def clear_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user:
        clear_history(update.effective_user.id)
    await send_html(update, premium_block("Cleared", "Conversation memory has been reset.", "🧹"), reply_markup=premium_keyboard())


async def callback_router(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not update.effective_user:
        return
    await query.answer()
    data = query.data or ""

    if data.startswith("style:"):
        style = data.split(":", 1)[1].strip()
        if style in CHAT_STYLE_PRESETS and query.message:
            user_styles[update.effective_user.id] = style
            await query.message.reply_html(
                premium_block("Style Configuration", f"Current style: <b>{esc(style)}</b>", "🎭"),
                reply_markup=premium_keyboard(),
            )
        return

    if data.startswith("mode:"):
        mode = data.split(":", 1)[1].strip()
        user_modes[update.effective_user.id] = mode
        if query.message:
            await query.message.reply_html(
                premium_block("Mode Configuration", f"Current mode: <b>{esc(mode)}</b>", "⚙️"),
                reply_markup=premium_keyboard(),
            )
        return

    if data == "help:image" and query.message:
        await query.message.reply_html(
            premium_block("Image Generator", "Example Usage: <code>image cyberpunk city at night</code>", "🖼"),
            reply_markup=premium_keyboard(),
        )
        return

    if data == "help:search" and query.message:
        await query.message.reply_html(
            premium_block("Search Engine", "Example Usage: <code>search ai news</code>", "🔎"),
            reply_markup=premium_keyboard(),
        )


# ============================================================
# Main Message Router
# ============================================================
async def message_router(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_message or not update.effective_user:
        return

    text = (update.effective_message.text or update.effective_message.caption or "").strip()
    if not text:
        return

    intent = detect_intent(text)
    mode = user_modes[update.effective_user.id]

    if intent.name == Intent.HELP:
        await start_cmd(update, context)
        return
    if intent.name == Intent.CLEAR:
        await clear_cmd(update, context)
        return
    if intent.name == Intent.STYLE:
        style = intent.payload.get("style", "premium")
        user_styles[update.effective_user.id] = style
        await send_html(update, premium_block("Style Configuration", f"Current style: <b>{esc(style)}</b>", "🎭"), reply_markup=premium_keyboard())
        return
    if intent.name == Intent.MODE:
        mode_value = intent.payload.get("mode", "auto")
        user_modes[update.effective_user.id] = mode_value
        await send_html(update, premium_block("Mode Configuration", f"Current mode: <b>{esc(mode_value)}</b>", "⚙️"), reply_markup=premium_keyboard())
        return

    if mode == "search" and intent.name == Intent.CHAT:
        await answer_search(update, context, text)
        return
    if mode == "image" and intent.name == Intent.CHAT:
        await answer_image(update, context, text)
        return
    if mode == "ff" and intent.name == Intent.CHAT:
        uid = UID_RE.search(text)
        await answer_ff(update, context, uid.group(0) if uid else "", extract_region(text))
        return
    if mode == "tiktok" and intent.name == Intent.CHAT:
        link = TIKTOK_RE.search(text)
        await answer_tiktok(update, context, link.group(0) if link else "")
        return
    if mode == "youtube" and intent.name == Intent.CHAT:
        link = YT_VIDEO_RE.search(text)
        await answer_youtube(update, context, link.group(0) if link else "")
        return

    if intent.name == Intent.TIKTOK:
        await answer_tiktok(update, context, intent.payload.get("url", ""))
        return
    if intent.name == Intent.YOUTUBE:
        await answer_youtube(update, context, intent.payload.get("url", ""))
        return
    if intent.name == Intent.FREE_FIRE:
        await answer_ff(update, context, intent.payload.get("uid", ""), intent.payload.get("region", FF_DEFAULT_REGION))
        return
    if intent.name == Intent.IMAGE:
        await answer_image(update, context, intent.payload.get("prompt", text))
        return
    if intent.name == Intent.SEARCH:
        await answer_search(update, context, intent.payload.get("query", text))
        return
    if intent.name == Intent.YT_CHANNEL:
        await answer_yt_channel(update, context, intent.payload.get("channel_id", ""))
        return
    if intent.name == Intent.INSTAGRAM:
        await answer_instagram(update, context, intent.payload.get("iid", ""))
        return
    if intent.name == Intent.TIKTOK_ADS:
        await answer_tiktok_ads(update, context)
        return
    if intent.name == Intent.FACEBOOK:
        await answer_facebook(update, context, intent.payload.get("query", ""))
        return
    if intent.name == Intent.BG_REMOVE:
        await answer_bg_remove(update, context, intent.payload.get("url", ""))
        return

    if HARD_MODE:
        uid_match = UID_RE.fullmatch(text) or (UID_RE.search(text) if len(text.split()) <= 4 else None)
        if uid_match and 7 <= len(uid_match.group(0)) <= 14:
            await answer_ff(update, context, uid_match.group(0), extract_region(text))
            return
        if any(x in text.lower() for x in ("news", "what is", "who is", "when is", "where is", "why ", "how ", "meaning of ")):
            await answer_search(update, context, text)
            return

    await answer_chat(update, context, text)


# ============================================================
# Startup / Shutdown
# ============================================================
async def on_startup(application: Application) -> None:
    await get_session(application)
    logger.info("Bot started successfully.")


async def on_shutdown(application: Application) -> None:
    await close_session(application)
    logger.info("Bot stopped successfully.")


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.exception("Update error occurred", exc_info=context.error)
    if isinstance(update, Update) and update.effective_chat:
        with contextlib.suppress(Exception):
            await update.effective_chat.send_message(
                premium_block("System Error", "A temporary error occurred. Please try again.", "⚠️"),
                parse_mode="HTML",
            )


def build_application() -> Application:
    return (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .rate_limiter(AIORateLimiter())
        .post_init(on_startup)
        .post_shutdown(on_shutdown)
        .build()
    )


def main() -> None:
    app = build_application()
    app.add_handler(CommandHandler("start", start_cmd))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CommandHandler("clear", clear_cmd))
    app.add_handler(CallbackQueryHandler(callback_router))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, message_router))
    app.add_error_handler(error_handler)
    app.run_polling(drop_pending_updates=True, allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
