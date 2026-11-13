from __future__ import annotations

import array
import json
import math
import os
import queue
import random
import re
import threading
import time
from pathlib import Path

import pygame

try:
    import vosk
except ImportError:
    vosk = None

try:
    import sounddevice as sd
except ImportError:
    sd = None

try:
    import pyttsx3
except ImportError:
    pyttsx3 = None

try:
    import speech_recognition as sr
except ImportError:
    sr = None


pygame.font.init()

BASE_DIR = Path(__file__).resolve().parent
BACKGROUND_PATH = BASE_DIR / "pirate_background.png"
MODEL_PATH = Path(
    os.environ.get(
        "VOSK_MODEL_PATH",
        str(BASE_DIR / "vosk-model-small-ru-0.22"),
    )
)

BASE_W, BASE_H = 1586, 992
ROWS, COLS = 10, 10
COLUMN_NAMES = "АБВГДЕЖЗИК"
TREASURE_COUNT = 7
WIN_SCORE = 4

CELL_W = CELL_H = 42
GAP_X = GAP_Y = 3
GRID_W = COLS * CELL_W + (COLS - 1) * GAP_X
GRID_H = ROWS * CELL_H + (ROWS - 1) * GAP_Y
GRID_X = 237
GRID_Y = 365
GRID_FRAME = pygame.Rect(150, 349, 620, 475)
RESTART_BUTTON = pygame.Rect(83, 850, 360, 72)
VOICE_BUTTON = pygame.Rect(913, 578, 580, 55)
STRATEGY_BUTTONS = {
    "tracker": pygame.Rect(912, 380, 185, 59),
    "flanker": pygame.Rect(1110, 380, 185, 59),
    "scanner": pygame.Rect(1308, 380, 185, 59),
}
SOUND_BUTTON = pygame.Rect(912, 918, 110, 30)
VOLUME_TRACK = pygame.Rect(1080, 928, 260, 8)

WHITE = (255, 249, 226)
CREAM = (255, 225, 159)
GOLD = (255, 190, 42)
GOLD_LIGHT = (255, 225, 119)
RED = (244, 86, 76)
BLUE = (60, 190, 235)
GREEN = (72, 205, 127)
CYAN = (89, 220, 235)
INK = (83, 50, 30)
OCEAN = (7, 74, 103)

FONT_NAME = next(
    (
        pygame.font.match_font(name)
        for name in ("segoeui", "dejavusans", "arial", "liberationsans")
        if pygame.font.match_font(name)
    ),
    None,
)
font_cache: dict[tuple[int, bool], pygame.font.Font] = {}
text_commands: list[tuple[str, float, float, int, tuple[int, int, int], bool, bool]] = []
canvas = pygame.Surface((BASE_W, BASE_H))
screen: pygame.Surface | None = None

MODE_NAMES = {
    "tracker": "Следопыт",
    "flanker": "Обход",
    "scanner": "Сканер",
}
MODE_DESCRIPTIONS = {
    "tracker": "Следопыт выбирает неисследованные клетки с самыми сильными тепловыми сигналами.",
    "flanker": "Обход расширяет соседнюю область, особенно рядом с собственными находками.",
    "scanner": "Сканер сравнивает сектора карты и исследует наиболее перспективное направление.",
}
CLUE_COLORS = {
    "ЖАРКО": RED,
    "ТЕПЛО": (239, 154, 45),
    "ХОЛОДНО": BLUE,
    "ЯСНО": GREEN,
}

LETTERS = {
    "а": 0, "альфа": 0,
    "б": 1, "бэ": 1, "бе": 1,
    "в": 2, "вэ": 2, "ве": 2,
    "г": 3, "гэ": 3, "ге": 3,
    "д": 4, "дэ": 4, "де": 4,
    "е": 5, "ё": 5, "е": 5,
    "ж": 6, "же": 6,
    "з": 7, "зэ": 7, "зе": 7,
    "и": 8, "икраткое": 8, "и краткое": 8,
    "к": 9, "ка": 9,
}
NUMBERS = {
    "один": 1, "одна": 1, "первый": 1, "первая": 1, "раз": 1,
    "два": 2, "две": 2, "второй": 2, "вторая": 2,
    "три": 3, "третий": 3, "третья": 3,
    "четыре": 4, "четвертый": 4, "четвертая": 4,
    "пять": 5, "пятый": 5, "пятая": 5,
    "шесть": 6, "шестой": 6, "шестая": 6,
    "семь": 7, "седьмой": 7, "седьмая": 7,
    "восемь": 8, "восьмой": 8, "восьмая": 8,
    "девять": 9, "девятый": 9, "девятая": 9,
    "десять": 10, "десятый": 10, "десятая": 10,
}

treasures: set[tuple[int, int]] = set()
revealed: dict[tuple[int, int], dict[str, object]] = {}
player_score = 0
ai_score = 0
player_moves = 0
ai_moves = 0
game_over = False
winner = ""
game_log: list[str] = []
pending_guess: str | None = None
guess_message = ""
ai_hint = ""
intel_cells: set[tuple[int, int]] = set()
ai_strategy = "scanner"
strategy_selected = False
ai_probabilities: dict[tuple[int, int], float] = {}
voice_enabled = False
voice_status = "МИКРОФОН ВЫКЛЮЧЕН"
recognized_text = "Ожидаю голосовую команду."
captain_response = "Капитан готов к экспедиции."
sound_enabled = True
volume = 0.45
paused = False
running = False
_speech_output: SpeechOutput | None = None
_sound_manager: SoundManager | None = None
_treasure_animations: dict[tuple[int, int], float] = {}
_last_sound: str | None = None


def get_font(size: int, bold: bool = False) -> pygame.font.Font:
    key = (max(8, int(size)), bool(bold))
    if key not in font_cache:
        font_cache[key] = pygame.font.Font(FONT_NAME, key[0])
        font_cache[key].set_bold(bold)
    return font_cache[key]


def draw_text(
    message: object,
    x: float,
    y: float,
    size: int = 14,
    color: tuple[int, int, int] = WHITE,
    bold: bool = False,
    center: bool = False,
) -> pygame.Rect:
    text = str(message)
    text_commands.append((text, x, y, int(size), color, bold, center))
    image = get_font(size, bold).render(text, True, color)
    rect = image.get_rect()
    if center:
        rect.center = (round(x), round(y))
    else:
        rect.topleft = (round(x), round(y))
    return rect


def draw_wrapped(
    message: object,
    x: float,
    y: float,
    width: int,
    size: int = 12,
    color: tuple[int, int, int] = WHITE,
    max_lines: int = 3,
    line_gap: int = 3,
) -> int:
    font = get_font(size)
    lines: list[str] = []
    current = ""
    for word in str(message).split():
        if font.size(word)[0] > width:
            if current:
                lines.append(current)
                current = ""
            fragment = ""
            for character in word:
                if font.size(fragment + character)[0] > width and fragment:
                    lines.append(fragment)
                    fragment = character
                else:
                    fragment += character
            current = fragment
            continue
        candidate = word if not current else current + " " + word
        if font.size(candidate)[0] <= width:
            current = candidate
        else:
            lines.append(current)
            current = word
    if current:
        lines.append(current)
    visible = lines[:max_lines]
    for index, line in enumerate(visible):
        draw_text(line, x, y + index * (size + line_gap), size, color)
    return len(visible) * (size + line_gap)


def rounded(
    surface: pygame.Surface,
    rect: pygame.Rect,
    color: tuple[int, int, int],
    radius: int = 8,
    border: tuple[int, int, int] | None = None,
    border_width: int = 1,
) -> None:
    pygame.draw.rect(surface, color, rect, border_radius=radius)
    if border is not None:
        pygame.draw.rect(
            surface, border, rect, border_width, border_radius=radius
        )


def draw_coin(surface: pygame.Surface, cx: float, cy: float, radius: int = 7) -> None:
    center = (round(cx), round(cy))
    pygame.draw.circle(surface, (107, 61, 27), (center[0], center[1] + 2), radius + 1)
    pygame.draw.circle(surface, GOLD, center, radius)
    pygame.draw.circle(surface, GOLD_LIGHT, (center[0] - max(1, radius // 4), center[1] - max(1, radius // 4)), max(2, radius // 2))
    pygame.draw.circle(surface, (202, 126, 26), center, radius, 1)


def draw_gem(
    surface: pygame.Surface,
    cx: float,
    cy: float,
    size: int = 7,
    kind: str = "blue",
) -> None:
    palettes = {
        "blue": ((15, 78, 171), (39, 165, 246), (164, 239, 255)),
        "green": ((0, 103, 65), (12, 192, 110), (157, 255, 194)),
        "red": ((145, 24, 43), (239, 56, 73), (255, 170, 160)),
        "purple": ((81, 43, 151), (155, 95, 239), (220, 188, 255)),
    }
    dark, bright, shine = palettes.get(kind, palettes["blue"])
    x, y, radius = round(cx), round(cy), max(3, int(size))
    points = [(x, y - radius), (x + radius, y - radius // 3),
              (x + radius // 2, y + radius), (x - radius // 2, y + radius),
              (x - radius, y - radius // 3)]
    pygame.draw.polygon(surface, dark, points)
    pygame.draw.polygon(surface, bright, [points[0], points[1], (x, y + 2)])
    pygame.draw.polygon(surface, shine, [points[0], points[4], (x, y + 2)])
    pygame.draw.polygon(surface, (11, 50, 94), points, 1)


def draw_small_chest(
    surface: pygame.Surface, cx: float, cy: float, scale: float = 1.0
) -> None:
    width = max(18, round(35 * scale))
    height = max(12, round(21 * scale))
    x, y = round(cx - width / 2), round(cy - height / 2)
    pygame.draw.ellipse(surface, (255, 224, 124), (x - 5, y - 6, width + 10, height + 12))
    pygame.draw.rect(surface, (83, 41, 22), (x - 1, y - 1, width + 2, height + 3), border_radius=4)
    pygame.draw.rect(surface, (148, 76, 32), (x, y, width, height), border_radius=4)
    pygame.draw.rect(surface, (191, 108, 47), (x + 3, y + 3, width - 6, height - 6), border_radius=3)
    pygame.draw.rect(surface, GOLD, (x + 4, y, 4, height), border_radius=1)
    pygame.draw.rect(surface, GOLD, (x + width - 8, y, 4, height), border_radius=1)
    pygame.draw.rect(surface, GOLD_LIGHT, (round(cx - 3), y + 4, 6, 8), border_radius=2)
    draw_coin(surface, cx - 9 * scale, y - 2 * scale, max(3, round(4 * scale)))
    draw_gem(surface, cx + 7 * scale, y - 5 * scale, max(3, round(4 * scale)), "blue")
    draw_gem(surface, cx - 4 * scale, y - 5 * scale, max(3, round(4 * scale)), "green")


def iter_grid_rects():
    for row in range(ROWS):
        for col in range(COLS):
            yield cell_rect(row, col)


def cell_rect(row: int, col: int) -> pygame.Rect:
    if not (0 <= row < ROWS and 0 <= col < COLS):
        raise ValueError(f"Invalid grid coordinate: {(row, col)}")
    return pygame.Rect(
        GRID_X + col * (CELL_W + GAP_X),
        GRID_Y + row * (CELL_H + GAP_Y),
        CELL_W,
        CELL_H,
    )


def cell_at(point: tuple[float, float]) -> tuple[int, int] | None:
    x, y = point
    col_step, row_step = CELL_W + GAP_X, CELL_H + GAP_Y
    col = math.floor((x - GRID_X) / col_step)
    row = math.floor((y - GRID_Y) / row_step)
    if not (0 <= row < ROWS and 0 <= col < COLS):
        return None
    return (row, col) if cell_rect(row, col).collidepoint(x, y) else None


def coord_name(pos: tuple[int, int]) -> str:
    row, col = pos
    if not (0 <= row < ROWS and 0 <= col < COLS):
        raise ValueError(f"Invalid grid coordinate: {pos}")
    return f"{COLUMN_NAMES[col]}{row + 1}"


def viewport_for(size: tuple[int, int]) -> pygame.Rect:
    width, height = size
    if width <= 0 or height <= 0:
        raise ValueError("Viewport dimensions must be positive")
    return pygame.Rect(0, 0, width, height)


def screen_to_design(
    point: tuple[float, float], viewport: pygame.Rect
) -> tuple[float, float] | None:
    if not viewport.collidepoint(point):
        return None
    return (
        (point[0] - viewport.x) * BASE_W / viewport.width,
        (point[1] - viewport.y) * BASE_H / viewport.height,
    )


def manhattan(a: tuple[int, int], b: tuple[int, int]) -> int:
    return abs(a[0] - b[0]) + abs(a[1] - b[1])


def clue_for(pos: tuple[int, int]) -> str:
    if not treasures:
        return "ЯСНО"
    distance = min(manhattan(pos, treasure) for treasure in treasures)
    if distance <= 2:
        return "ЖАРКО"
    if distance <= 4:
        return "ТЕПЛО"
    if distance <= 6:
        return "ХОЛОДНО"
    return "ЯСНО"


def update_clues() -> None:
    for pos, tile in revealed.items():
        if not tile["treasure"]:
            tile["clue"] = clue_for(pos)


def quadrant(pos: tuple[int, int]) -> tuple[int, int]:
    return min(1, pos[0] // 5), min(1, pos[1] // 5)


def quadrant_counts(owner: str | None = None) -> dict[tuple[int, int], int]:
    counts = {(row, col): 0 for row in range(2) for col in range(2)}
    for pos, tile in revealed.items():
        if owner is None or tile["owner"] == owner:
            counts[quadrant(pos)] += 1
    return counts


def determine_ai_mode() -> str:
    if strategy_selected:
        return ai_strategy
    clues = [tile["clue"] for tile in revealed.values() if not tile["treasure"]]
    if clues.count("ЖАРКО") or clues.count("ТЕПЛО") >= 2:
        return "tracker"
    player_cells = [pos for pos, tile in revealed.items() if tile["owner"] == "player"]
    if len(player_cells) >= 3:
        counts = quadrant_counts("player")
        if max(counts.values()) / len(player_cells) >= 0.6:
            return "flanker"
    return "scanner"


def _clue_score(clue: object, distance: int) -> float:
    if clue == "ЖАРКО":
        return 2.8 if distance <= 2 else (-2.2 if distance > 4 else 0.3)
    if clue == "ТЕПЛО":
        return 2.2 if 2 < distance <= 4 else (-1.6 if distance <= 2 else -0.5)
    if clue == "ХОЛОДНО":
        return 1.2 if 4 < distance <= 6 else (-1.3 if distance <= 4 else 0.1)
    if clue == "ЯСНО":
        return 1.0 if distance > 6 else -0.8
    return 0.0


def ranked_candidates(mode: str):
    candidates: list[tuple[float, tuple[int, int]]] = []
    clue_cells = [
        (pos, tile["clue"])
        for pos, tile in revealed.items()
        if not tile["treasure"] and tile["clue"]
    ]
    all_counts = quadrant_counts()
    player_counts = quadrant_counts("player")
    row_counts = [0] * ROWS
    col_counts = [0] * COLS
    for row, col in revealed:
        row_counts[row] += 1
        col_counts[col] += 1
    quadrant_totals: dict[tuple[int, int], float] = {}
    evidence_scores: dict[tuple[int, int], float] = {}
    strategy_scores: dict[tuple[int, int], float] = {}
    for region in all_counts:
        options = [
            (row, col)
            for row in range(ROWS)
            for col in range(COLS)
            if quadrant((row, col)) == region and (row, col) not in revealed
        ]
        evidence = sum(
            max(0.0, _clue_score(tile["clue"], manhattan(pos, clue_pos)))
            for clue_pos, tile in revealed.items()
            if not tile["treasure"] and tile["clue"]
            for pos in options
        )
        quadrant_totals[region] = evidence / max(1, len(options))

    for row in range(ROWS):
        for col in range(COLS):
            pos = (row, col)
            if pos in revealed:
                continue
            evidence_score = 0.0
            for clue_pos, clue in clue_cells:
                evidence_score += _clue_score(clue, manhattan(pos, clue_pos))
            strategy_score = 0.0

            if mode == "flanker":
                frontier = min(
                    (manhattan(pos, seen) for seen in revealed),
                    default=0,
                )
                own_frontier = min(
                    (manhattan(pos, seen) for seen, tile in revealed.items()
                     if tile["owner"] == "ai"),
                    default=4,
                )
                strategy_score += max(0, 4 - own_frontier) * 0.8
                strategy_score += 1.5 if frontier == 1 else (-0.3 * frontier)
                strategy_score += max(0, 2 - player_counts[quadrant(pos)]) * 0.25
            elif mode == "scanner":
                strategy_score += quadrant_totals[quadrant(pos)] * 0.9
                strategy_score += (max(all_counts.values()) - all_counts[quadrant(pos)]) * 0.08
                strategy_score -= row_counts[row] * 0.015 + col_counts[col] * 0.01

            evidence_scores[pos] = evidence_score
            strategy_scores[pos] = strategy_score
            candidates.append((evidence_score + strategy_score + random.random() * 0.05, pos))
    candidates.sort(key=lambda item: item[0], reverse=True)
    if candidates:
        prior = min(0.98, len(treasures) / len(candidates))
        prior_odds = prior / max(0.02, 1.0 - prior)
        raw_probabilities = {
            pos: prior_odds * math.exp(
                max(-3.0, min(3.0, evidence_scores[pos] * 0.45))
            )
            for _, pos in candidates
        }
        scale = len(treasures) / max(0.0001, sum(raw_probabilities.values()))
        ai_probabilities.clear()
        ai_probabilities.update(
            (pos, min(0.99, probability * scale))
            for pos, probability in raw_probabilities.items()
        )
    return candidates


def choose_ai_cell(mode: str) -> tuple[int, int] | None:
    global ai_hint
    ranked = ranked_candidates(mode)
    if not ranked:
        ai_hint = "На карте не осталось неисследованных клеток."
        return None
    best = ranked[0][1]
    probability = ai_probabilities.get(best, 0.5)
    supporting = [
        str(clue).lower()
        for _, clue in [
            (pos, tile["clue"])
            for pos, tile in revealed.items()
            if not tile["treasure"] and tile["clue"]
        ]
    ]
    evidence = ", ".join(supporting[-2:]) if supporting else "пока недостаточно сигналов"
    global_hint = (
        f"{MODE_NAMES[mode]}: {coord_name(best)} — приоритетная клетка "
        f"(оценка вероятности {probability:.0%}); учитываю {evidence}."
    )
    ai_hint = global_hint
    return best


def add_log(message: str) -> None:
    game_log.append(message)
    del game_log[:-8]


def reset_game() -> None:
    global treasures, revealed, player_score, ai_score, player_moves, ai_moves
    global game_over, winner, game_log, pending_guess, guess_message, ai_hint
    global intel_cells, ai_strategy, strategy_selected, ai_probabilities
    global _treasure_animations
    all_cells = [(row, col) for row in range(ROWS) for col in range(COLS)]
    treasures = set(random.sample(all_cells, TREASURE_COUNT))
    revealed = {}
    player_score = ai_score = player_moves = ai_moves = 0
    game_over = False
    winner = ""
    game_log = []
    pending_guess = None
    guess_message = "Выберите клетку на карте или отдайте приказ голосом."
    ai_hint = "ИИ оценивает сигналы, историю ходов и свободные сектора карты."
    intel_cells = set()
    ai_strategy = "scanner"
    strategy_selected = False
    ai_probabilities = {}
    _treasure_animations = {}
    add_log("Экспедиция началась: на островах спрятано семь сокровищ.")
    add_log("Найдите четыре сокровища раньше пиратского соперника.")


def finish_if_needed() -> bool:
    global game_over, winner
    if player_score >= WIN_SCORE:
        game_over, winner = True, "player"
        add_log("Победа! Вы нашли четыре сокровища первыми.")
    elif ai_score >= WIN_SCORE:
        game_over, winner = True, "ai"
        add_log("Пиратский ИИ первым собрал четыре сокровища.")
    elif not treasures:
        game_over = True
        winner = "player" if player_score > ai_score else "ai" if ai_score > player_score else "draw"
        add_log("Экспедиция завершена: все сокровища найдены.")
    return game_over


def search_cell(pos: tuple[int, int], owner: str) -> bool:
    global player_score, ai_score, player_moves, ai_moves, _last_sound
    row, col = pos
    if owner not in ("player", "ai") or not (0 <= row < ROWS and 0 <= col < COLS):
        return False
    if pos in revealed:
        return False
    found = pos in treasures
    if owner == "player":
        player_moves += 1
    else:
        ai_moves += 1
    revealed[pos] = {"owner": owner, "treasure": found, "clue": None}
    if found:
        treasures.remove(pos)
        if owner == "player":
            player_score += 1
            add_log(f"Вы нашли сундук с сокровищами на острове {coord_name(pos)}!")
        else:
            ai_score += 1
            add_log(f"Пиратский ИИ нашёл сокровище на острове {coord_name(pos)}.")
        _treasure_animations[pos] = time.monotonic() + 1.5
        _last_sound = "treasure"
    else:
        update_clues()
        clue = str(revealed[pos]["clue"])
        who = "Вы" if owner == "player" else "ИИ"
        add_log(f"{who}: остров {coord_name(pos)} — сигнал «{clue.lower()}».")
        _last_sound = "open"
    update_clues()
    return True


def do_player_move(pos: tuple[int, int]) -> bool:
    global pending_guess, guess_message, intel_cells, ai_probabilities, ai_strategy
    if game_over or not search_cell(pos, "player"):
        if pos in revealed:
            guess_message = f"Остров {coord_name(pos)} уже исследован."
        return False
    pending_guess = None
    intel_cells.clear()
    ai_probabilities.clear()
    if finish_if_needed():
        guess_message = "Экспедиция завершена. Начните новую игру."
        return True
    mode = determine_ai_mode()
    if not strategy_selected:
        ai_strategy = mode
    ai_pos = choose_ai_cell(mode)
    if ai_pos is not None:
        search_cell(ai_pos, "ai")
    finish_if_needed()
    intel_cells = {pos for _, pos in ranked_candidates(mode)[:3]}
    return True


def select_strategy(mode: str) -> bool:
    global ai_strategy, strategy_selected, pending_guess, guess_message
    if mode not in MODE_NAMES:
        return False
    ai_strategy = mode
    strategy_selected = True
    pending_guess = mode
    guess_message = f"Стратегия «{MODE_NAMES[mode]}» активирована."
    add_log(f"Активирована стратегия ИИ: {MODE_NAMES[mode]}.")
    return True


class VoiceListener:
    def __init__(self) -> None:
        self.messages: queue.Queue[tuple[str, str, str]] = queue.Queue()
        self._stop = threading.Event()
        self._enabled = threading.Event()
        self._thread: threading.Thread | None = None
        self._model: object | None = None

    def start(self) -> None:
        if self._thread is None or not self._thread.is_alive():
            self._stop.clear()
            self._thread = threading.Thread(
                target=self._run, name="pirate-voice-listener", daemon=True
            )
            self._thread.start()

    def set_enabled(self, enabled: bool) -> None:
        if enabled:
            self.start()
            self._enabled.set()
        else:
            self._enabled.clear()
            self.messages.put(("status", "", "МИКРОФОН ВЫКЛЮЧЕН"))

    def stop(self, timeout: float = 3.0) -> bool:
        self._stop.set()
        self._enabled.clear()
        if self._thread is not None:
            self._thread.join(timeout)
            return not self._thread.is_alive()
        return True

    def _emit_status(self, message: str) -> None:
        self.messages.put(("status", "", message))

    def _emit_command(self, command: str) -> None:
        self.messages.put(("command", command, ""))

    def _run(self) -> None:
        self._preflight()
        while not self._stop.is_set():
            if not self._enabled.wait(0.1):
                continue
            if self._stop.is_set() or not self._enabled.is_set():
                continue
            if vosk is not None and sd is not None and MODEL_PATH.is_dir():
                self._listen_vosk()
            else:
                if vosk is None or sd is None or not MODEL_PATH.is_dir():
                    self._emit_status(
                        f"Русская модель Vosk не найдена: {MODEL_PATH}"
                    )
                self._listen_fallback()

    def _preflight(self) -> None:
        if vosk is None or not MODEL_PATH.is_dir():
            self._emit_status(f"Русская модель Vosk не найдена: {MODEL_PATH}")
        if sd is None:
            self._emit_status("sounddevice не установлен: микрофон недоступен.")
            return
        try:
            sd.query_devices(kind="input")
        except Exception as exc:
            self._emit_status(f"Микрофон недоступен: {exc}")

    def _listen_vosk(self) -> None:
        try:
            if self._model is None:
                self._emit_status("Загружаю русскую модель Vosk…")
                self._model = vosk.Model(str(MODEL_PATH))
            recognizer = vosk.KaldiRecognizer(self._model, 16000)
            audio_queue: queue.Queue[bytes] = queue.Queue()

            def receive_audio(indata, _, *callback_args) -> None:
                status = callback_args[-1]
                if status:
                    self._emit_status(f"Микрофон: {status}")
                audio_queue.put(bytes(indata))

            self._emit_status("МИКРОФОН: ВКЛЮЧЁН — слушаю по-русски")
            with sd.RawInputStream(
                samplerate=16000,
                blocksize=8000,
                dtype="int16",
                channels=1,
                callback=receive_audio,
            ):
                while self._enabled.is_set() and not self._stop.is_set():
                    try:
                        chunk = audio_queue.get(timeout=0.25)
                    except queue.Empty:
                        continue
                    if recognizer.AcceptWaveform(chunk):
                        phrase = json.loads(recognizer.Result()).get("text", "").strip()
                        if phrase:
                            self._emit_status("ОБРАБАТЫВАЮ КОМАНДУ")
                            self._emit_command(phrase)
                    else:
                        partial = json.loads(recognizer.PartialResult()).get("partial", "")
                        if partial:
                            self._emit_status(f"СЛУШАЮ: {partial.upper()}")
        except Exception as exc:
            self._emit_status(f"Микрофон недоступен: {exc}")
            self._enabled.clear()

    def _listen_fallback(self) -> None:
        if sr is None:
            self._emit_status("Распознавание речи не установлено: установите Vosk и sounddevice.")
            self._enabled.clear()
            return
        try:
            recognizer = sr.Recognizer()
            recognizer.pause_threshold = 0.65
            self._emit_status("Запасное распознавание: подключаю микрофон…")
            with sr.Microphone() as source:
                recognizer.adjust_for_ambient_noise(source, duration=0.4)
                self._emit_status("МИКРОФОН: ВКЛЮЧЁН — говорите команду")
                while self._enabled.is_set() and not self._stop.is_set():
                    try:
                        audio = recognizer.listen(
                            source, timeout=1, phrase_time_limit=2
                        )
                    except sr.WaitTimeoutError:
                        continue
                    self._emit_status("ОБРАБАТЫВАЮ КОМАНДУ")
                    try:
                        text = recognizer.recognize_google(
                            audio, language="ru-RU"
                        ).strip().lower()
                        self._emit_command(text)
                    except sr.UnknownValueError:
                        self._emit_status("Речь не распознана — повторите команду.")
                    except sr.RequestError:
                        self._emit_status("Нет интернет-соединения для запасного распознавания.")
                        self._enabled.clear()
        except Exception as exc:
            self._emit_status(f"Микрофон недоступен: {exc}")
            self._enabled.clear()


class SpeechOutput:
    def __init__(self) -> None:
        self._messages: queue.Queue[str | None] = queue.Queue()
        self._thread: threading.Thread | None = None
        self._stop = threading.Event()
        self.error: str | None = None

    def start(self) -> None:
        if pyttsx3 is None:
            self.error = "Озвучивание недоступно: установите pyttsx3."
            return
        if self._thread is None or not self._thread.is_alive():
            self._stop.clear()
            self._thread = threading.Thread(
                target=self._run, name="pirate-captain-voice", daemon=True
            )
            self._thread.start()

    def say(self, text: str) -> None:
        if self._thread is None or not self._thread.is_alive():
            self.start()
        if self._thread is not None and self._thread.is_alive():
            self._messages.put(text)

    def stop(self) -> None:
        self._stop.set()
        self._messages.put(None)
        if self._thread is not None:
            self._thread.join(1.0)

    def _run(self) -> None:
        engine = None
        try:
            engine = pyttsx3.init()
            engine.setProperty("rate", 165)
            voices = engine.getProperty("voices")
            for voice in voices:
                if "ru" in (voice.id + " " + voice.name).lower():
                    engine.setProperty("voice", voice.id)
                    break
            while not self._stop.is_set():
                try:
                    text = self._messages.get(timeout=0.2)
                except queue.Empty:
                    continue
                if text is None:
                    break
                engine.say(text)
                engine.runAndWait()
        except Exception as exc:
            self.error = f"Не удалось озвучить ответ капитана: {exc}"
        finally:
            if engine is not None:
                engine.stop()


class SoundManager:
    def __init__(self) -> None:
        self.music: pygame.mixer.Sound | None = None
        self.waves: pygame.mixer.Sound | None = None
        self.music_channel: pygame.mixer.Channel | None = None
        self.wave_channel: pygame.mixer.Channel | None = None
        self.effects: dict[str, pygame.mixer.Sound] = {}
        self.available = False
        self.error: str | None = None
        try:
            if not pygame.mixer.get_init():
                pygame.mixer.init(frequency=22050, size=-16, channels=2, buffer=512)
            self.music = self._make_melody()
            self.waves = self._make_waves()
            self.effects = {
                "click": self._tone(660, 0.07),
                "open": self._tone(390, 0.18),
                "treasure": self._chime(),
                "hint": self._tone(880, 0.14),
            }
            self.available = True
        except pygame.error as exc:
            self.error = f"Звук недоступен: {exc}"

    def _samples(self, frequencies: list[float], duration: float) -> bytes:
        sample_rate = 22050
        frames = int(sample_rate * duration)
        audio = array.array("h")
        for frame in range(frames):
            time_value = frame / sample_rate
            envelope = min(1.0, frame / 350) * min(1.0, (frames - frame) / 500)
            value = sum(
                math.sin(2 * math.pi * frequency * time_value) / len(frequencies)
                for frequency in frequencies
            )
            sample = int(12000 * value * envelope)
            audio.extend((sample, sample))
        return audio.tobytes()

    def _tone(self, frequency: float, duration: float) -> pygame.mixer.Sound:
        return pygame.mixer.Sound(buffer=self._samples([frequency], duration))

    def _chime(self) -> pygame.mixer.Sound:
        return pygame.mixer.Sound(buffer=self._samples([784, 988, 1175], 0.65))

    def _make_melody(self) -> pygame.mixer.Sound:
        notes = [196, 247, 294, 247, 220, 262, 330, 262]
        sample_rate = 22050
        audio = array.array("h")
        for frequency in notes:
            duration = 0.48
            for frame in range(int(sample_rate * duration)):
                phase = frame / sample_rate
                envelope = min(1.0, frame / 500) * min(1.0, (duration * sample_rate - frame) / 800)
                sample = int(1100 * math.sin(2 * math.pi * frequency * phase) * envelope)
                audio.extend((sample, sample))
        return pygame.mixer.Sound(buffer=audio.tobytes())

    def _make_waves(self) -> pygame.mixer.Sound:
        sample_rate = 22050
        duration = 3.0
        audio = array.array("h")
        for frame in range(int(sample_rate * duration)):
            moment = frame / sample_rate
            swell = 0.55 + 0.45 * math.sin(2 * math.pi * 0.22 * moment)
            sample = round(
                swell * (
                    280 * math.sin(2 * math.pi * 42 * moment)
                    + 180 * math.sin(2 * math.pi * 57 * moment)
                )
            )
            audio.extend((sample, sample))
        return pygame.mixer.Sound(buffer=audio.tobytes())

    def play(self, sound: str, enabled: bool, volume_level: float) -> None:
        if not enabled or not self.available:
            return
        selected = self.effects.get(sound)
        if selected is not None:
            selected.set_volume(max(0.0, min(1.0, volume_level)))
            selected.play()

    def set_music(self, enabled: bool, volume_level: float) -> None:
        if not self.available or self.music is None or self.waves is None:
            return
        self.music.set_volume(max(0.0, min(0.2, volume_level * 0.2)))
        self.waves.set_volume(max(0.0, min(0.12, volume_level * 0.12)))
        if enabled:
            if self.music_channel is None or not self.music_channel.get_busy():
                self.music_channel = self.music.play(loops=-1)
            if self.wave_channel is None or not self.wave_channel.get_busy():
                self.wave_channel = self.waves.play(loops=-1)
        else:
            if self.music_channel is not None:
                self.music_channel.stop()
            if self.wave_channel is not None:
                self.wave_channel.stop()


def _set_captain_response(text: str, speak: bool = True) -> None:
    global captain_response
    captain_response = text
    if speak and _speech_output is not None:
        _speech_output.say(text)
        if _speech_output.error:
            captain_response = _speech_output.error


def parse_voice_coordinate(command: str) -> tuple[int, int] | None:
    if not any(
        word in command.lower()
        for word in ("исследуй", "открой", "найди", "проверь", "клетку", "остров")
    ):
        return None
    cleaned = re.sub(r"[^а-яёa-z0-9\s-]", " ", command.lower().replace("ё", "е"))
    tokens = cleaned.split()
    columns: list[int] = []
    rows: list[int] = []
    for token in tokens:
        match = re.fullmatch(r"([а-яa-z])(\d{1,2})", token)
        if match:
            letter, number_text = match.groups()
            if letter in LETTERS:
                columns.append(LETTERS[letter])
                rows.append(int(number_text))
            continue
        if token in LETTERS:
            columns.append(LETTERS[token])
        if token in NUMBERS:
            rows.append(NUMBERS[token])
        elif token.isdigit():
            rows.append(int(token))
        elif token == "десятый":
            rows.append(10)
    if len(columns) != 1 or len(rows) != 1:
        return None
    row, col = rows[0], columns[0]
    if 1 <= row <= ROWS and 0 <= col < COLS:
        return row - 1, col
    return None


def handle_voice_command(command: str) -> str:
    global pending_guess, guess_message, voice_status, recognized_text
    global sound_enabled, volume, voice_enabled
    command = command.lower().strip()
    recognized_text = command.upper()
    if any(phrase in command for phrase in ("новая экспедиция", "начать заново", "перезапуск игры")):
        reset_game()
        add_log("Новая экспедиция запущена голосовой командой.")
        voice_status = "МИКРОФОН: ВКЛЮЧЁН"
        _set_captain_response("Новая экспедиция началась, капитан. Удачи в поисках!")
        return "executed"
    if command in ("выход", "закрыть игру", "выйти из игры"):
        _set_captain_response("До новых встреч, капитан!")
        return "exit"
    if "выключи звук" in command or "выключи музыку" in command:
        sound_enabled = False
        if _sound_manager is not None:
            _sound_manager.set_music(False, volume)
        _set_captain_response("Звук выключен.")
        return "executed"
    if "включи звук" in command or "включи музыку" in command:
        sound_enabled = True
        if _sound_manager is not None:
            _sound_manager.set_music(True, volume)
        _set_captain_response("Звук включён.")
        return "executed"
    if "выключи голосовое управление" in command or "выключи микрофон" in command or "отключи микрофон" in command:
        voice_enabled = False
        voice_status = "МИКРОФОН: ВЫКЛЮЧЕН"
        _set_captain_response("Голосовое управление выключено.")
        return "executed"
    if "включи голосовое управление" in command or "включи микрофон" in command or "запусти микрофон" in command:
        voice_enabled = True
        voice_status = "МИКРОФОН: ВКЛЮЧЁН"
        _set_captain_response("Слушаю вашу команду, капитан.")
        return "executed"
    if "покажи карту" in command:
        _set_captain_response("Карта островов перед вами, капитан.")
        return "executed"
    if "сколько" in command and ("сокровищ" in command or "осталось" in command):
        _set_captain_response(f"На карте осталось сокровищ: {len(treasures)}.")
        return "executed"
    if "повтори" in command and ("анализ" in command or "последний" in command):
        global _last_sound
        _last_sound = "hint"
        _set_captain_response(ai_hint)
        return "executed"
    strategies = {
        "следопыт": "tracker",
        "обход": "flanker",
        "сканер": "scanner",
    }
    for name, mode in strategies.items():
        if name in command:
            select_strategy(mode)
            voice_status = f"СТРАТЕГИЯ: {MODE_NAMES[mode].upper()}"
            _set_captain_response(f"Стратегия {MODE_NAMES[mode]} активирована.")
            return "executed"
    if any(word in command for word in ("исследуй", "открой", "найди", "проверь", "клетку", "остров")):
        pos = parse_voice_coordinate(command)
        if pos is None:
            guess_message = "Не удалось определить координаты. Скажите, например: «Открой клетку Б три»."
            voice_status = "КООРДИНАТЫ НЕ РАСПОЗНАНЫ"
            _set_captain_response("Не удалось распознать координаты. Повторите ещё раз.")
            return "invalid_coordinate"
        if game_over:
            _set_captain_response("Экспедиция завершена. Начните новую.")
            return "game_over"
        if pos in revealed:
            _set_captain_response(f"Клетка {coord_name(pos)} уже исследована.")
            return "already_explored"
        moved = do_player_move(pos)
        if not moved:
            return "invalid_coordinate"
        tile = revealed.get(pos)
        if tile is None:
            response = f"Команда распознана. Исследую клетку {coord_name(pos)}."
        elif tile["treasure"]:
            response = f"Команда распознана. В клетке {coord_name(pos)} найдено сокровище!"
        else:
            response = f"В клетке {coord_name(pos)} пусто. Получен сигнал {str(tile['clue']).lower()}."
        voice_status = f"ИССЛЕДОВАНА КЛЕТКА {coord_name(pos)}"
        _set_captain_response(response)
        return "executed"
    voice_status = "КОМАНДА НЕ РАСПОЗНАНА"
    _set_captain_response("Не удалось распознать команду. Повторите ещё раз.")
    return "unrecognized"


def draw_tile_overlay(surface: pygame.Surface, pos: tuple[int, int], tile: dict[str, object]) -> None:
    rect = cell_rect(*pos)
    if tile["treasure"]:
        fill = (247, 210, 117)
        border = GOLD_LIGHT
    else:
        fill = {
            "ЖАРКО": (255, 190, 157),
            "ТЕПЛО": (255, 220, 144),
            "ХОЛОДНО": (164, 219, 234),
            "ЯСНО": (184, 225, 158),
        }.get(str(tile["clue"]), (220, 215, 164))
        border = (255, 245, 186)
    rounded(surface, rect, fill, 7, border, 2)
    owner_color = BLUE if tile["owner"] == "player" else RED
    pygame.draw.circle(surface, owner_color, (rect.x + 7, rect.y + 7), 3)
    if tile["treasure"]:
        remaining = _treasure_animations.get(pos, 0) - time.monotonic()
        pulse = max(0.75, 1.0 + 0.18 * math.sin((1.5 - remaining) * 12)) if remaining > 0 else 0.8
        draw_small_chest(surface, rect.centerx, rect.centery + 1, pulse)
        if remaining > 0:
            pygame.draw.circle(surface, GOLD_LIGHT, rect.center, 19, 2)
    else:
        pygame.draw.ellipse(surface, (15, 127, 148), (rect.centerx - 15, rect.centery - 7, 30, 17))
        pygame.draw.ellipse(surface, (242, 203, 128), (rect.centerx - 14, rect.centery - 10, 28, 17))
        pygame.draw.ellipse(surface, (94, 173, 75), (rect.centerx - 10, rect.centery - 9, 20, 11))
        label = str(tile["clue"] or "")
        if label:
            color = CLUE_COLORS.get(label, INK)
            pygame.draw.circle(surface, color, (rect.right - 6, rect.bottom - 6), 4)
            draw_text(label, rect.centerx, rect.bottom - 5, 7, color, True, True)


def _draw_button(surface: pygame.Surface, rect: pygame.Rect, label: str, selected: bool = False, size: int = 14) -> None:
    base = (70, 127, 145) if not selected else (116, 87, 36)
    rounded(surface, rect, base, 13, GOLD_LIGHT if selected else (201, 145, 55), 3)
    pygame.draw.line(surface, (255, 239, 177), (rect.x + 14, rect.y + 6), (rect.right - 14, rect.y + 6), 1)
    draw_text(label, rect.centerx, rect.centery, size, WHITE, True, True)


def _draw_scene(
    background: pygame.Surface,
    listener: VoiceListener,
    mouse: tuple[float, float] | None = None,
    paused_state: bool = False,
) -> None:
    global canvas
    text_commands.clear()
    canvas.blit(pygame.transform.smoothscale(background, (BASE_W, BASE_H)), (0, 0))

    draw_text("ОХОТНИКИ", 305, 76, 43, GOLD_LIGHT, True, True)
    draw_text("ЗА СОКРОВИЩАМИ", 305, 119, 39, WHITE, True, True)
    draw_text("Разведывай • Анализируй • Побеждай", 305, 157, 17, CREAM, True, True)
    draw_text("ЦЕЛЬ ЭКСПЕДИЦИИ", 1300, 43, 18, INK, True)
    draw_wrapped(f"Найдите {WIN_SCORE} сокровища раньше соперника. На островах спрятано {TREASURE_COUNT}.", 1300, 75, 218, 15, INK, 4)

    draw_text("ИГРОК", 237, 226, 17, WHITE, True, True)
    draw_text(f"{player_score} / {WIN_SCORE}", 237, 250, 28, WHITE, True, True)
    draw_text("Ваши находки", 237, 281, 12, CREAM, False, True)
    draw_text("ПИРАТСКИЙ ИИ", 550, 226, 17, WHITE, True, True)
    draw_text(f"{ai_score} / {WIN_SCORE}", 550, 250, 28, WHITE, True, True)
    draw_text("Находки соперника", 550, 281, 12, CREAM, False, True)
    draw_text("ОСТАЛОСЬ", 747, 241, 13, INK, True, True)
    draw_text(str(len(treasures)), 775, 270, 29, INK, True, True)
    draw_coin(canvas, 733, 271, 8)

    draw_text("КАРТА ОСТРОВОВ", 141, 325, 21, INK, True)
    for col, letter in enumerate(COLUMN_NAMES):
        draw_text(letter, GRID_X + col * (CELL_W + GAP_X) + CELL_W // 2, GRID_Y - 15, 13, INK, True, True)
    for row in range(ROWS):
        draw_text(str(row + 1), GRID_X - 20, GRID_Y + row * (CELL_H + GAP_Y) + CELL_H // 2, 12, INK, True, True)

    hovered = cell_at(mouse) if mouse else None
    for row in range(ROWS):
        for col in range(COLS):
            pos = (row, col)
            rect = cell_rect(row, col)
            if pos in revealed:
                draw_tile_overlay(canvas, pos, revealed[pos])
            else:
                pygame.draw.circle(canvas, (120, 225, 239), rect.center, 7, 2)
                pygame.draw.circle(canvas, (255, 234, 173), rect.center, 2)
            if pos in intel_cells and pos not in revealed:
                pygame.draw.rect(canvas, GOLD_LIGHT, rect.inflate(4, 4), 2, border_radius=8)
            if pos == hovered and pos not in revealed:
                pygame.draw.rect(canvas, GOLD_LIGHT, rect.inflate(4, 4), 3, border_radius=8)

    draw_text("ЦЕНТР НАБЛЮДЕНИЯ ИИ", 910, 224, 21, GOLD_LIGHT, True)
    draw_text(f"Стратегия: {MODE_NAMES[ai_strategy]}", 910, 254, 14, CYAN, True)
    draw_text("ПОСЛЕДНИЙ АНАЛИЗ", 910, 281, 14, CYAN, True)
    draw_wrapped(ai_hint, 910, 304, 575, 13, WHITE, 3, 3)

    draw_text("ВЫБЕРИТЕ СТРАТЕГИЮ ИИ", 910, 355, 14, GOLD_LIGHT, True)
    for mode, rect in STRATEGY_BUTTONS.items():
        _draw_button(canvas, rect, MODE_NAMES[mode].upper(), mode == ai_strategy, 13)
    draw_wrapped(guess_message, 912, 448, 575, 12, WHITE, 2, 2)

    draw_text("ГОЛОСОВОЕ УПРАВЛЕНИЕ", 910, 499, 16, GOLD_LIGHT, True)
    is_listening = listener._enabled.is_set()
    status_color = GREEN if is_listening else (255, 190, 128)
    draw_text(voice_status, 910, 523, 12, status_color, True)
    _draw_button(canvas, VOICE_BUTTON, "ВЫКЛЮЧИТЬ ГОЛОСОВОЕ УПРАВЛЕНИЕ" if voice_enabled else "ВКЛЮЧИТЬ ГОЛОСОВОЕ УПРАВЛЕНИЕ", voice_enabled, 14)
    draw_text("ВЫ РАСПОЗНАНЫ:", 912, 646, 11, GOLD_LIGHT, True)
    draw_wrapped(f"«{recognized_text}»", 1032, 646, 460, 12, WHITE, 2, 2)
    draw_text("ОТВЕТ КАПИТАНА:", 912, 682, 11, GOLD_LIGHT, True)
    draw_wrapped(f"«{captain_response}»", 1032, 682, 460, 12, WHITE, 2, 2)

    draw_text("КАК ЧИТАТЬ СИГНАЛЫ", 910, 733, 14, GOLD_LIGHT, True)
    legend = [
        ("ЖАРКО", RED, "до 2 шагов"),
        ("ТЕПЛО", (239, 154, 45), "3–4 шага"),
        ("ХОЛОДНО", BLUE, "5–6 шагов"),
        ("ЯСНО", GREEN, "дальше 6 шагов"),
    ]
    for index, (label, color, explanation) in enumerate(legend):
        y = 759 + index * 24
        pygame.draw.circle(canvas, color, (915, y + 7), 5)
        draw_text(label, 927, y, 10, color, True)
        draw_text(explanation, 1002, y, 10, WHITE)

    draw_text("ЖУРНАЛ ЭКСПЕДИЦИИ", 1212, 733, 14, GOLD_LIGHT, True)
    for index, entry in enumerate(game_log[-5:]):
        y = 760 + index * 27
        pygame.draw.circle(canvas, GOLD if "нашли" in entry.lower() else GREEN, (1215, y + 6), 3)
        draw_wrapped(entry, 1226, y, 266, 10, WHITE, 2, 1)

    _draw_button(canvas, RESTART_BUTTON, "НОВАЯ ЭКСПЕДИЦИЯ", False, 16)
    draw_text("Кликните по клетке, чтобы искать", 623, 895, 11, INK, True, True)
    draw_text("Голос: «Открой клетку БЭ ТРИ»", 623, 920, 11, INK, False, True)
    draw_text("ЗВУК", 913, 899, 12, GOLD_LIGHT, True)
    _draw_button(canvas, SOUND_BUTTON, "ВКЛ" if sound_enabled else "ВЫКЛ", sound_enabled, 10)
    pygame.draw.rect(canvas, (88, 52, 30), VOLUME_TRACK, border_radius=4)
    pygame.draw.rect(canvas, GOLD_LIGHT, (VOLUME_TRACK.x, VOLUME_TRACK.y, round(VOLUME_TRACK.width * volume), VOLUME_TRACK.height), border_radius=4)
    pygame.draw.circle(canvas, WHITE, (VOLUME_TRACK.x + round(VOLUME_TRACK.width * volume), VOLUME_TRACK.centery), 9)
    draw_text(f"ГРОМКОСТЬ {round(volume * 100)}%", VOLUME_TRACK.right + 15, 920, 10, GOLD_LIGHT)

    if game_over:
        shade = pygame.Surface((BASE_W, BASE_H), pygame.SRCALPHA)
        shade.fill((3, 31, 48, 185))
        canvas.blit(shade, (0, 0))
        box = pygame.Rect(385, 365, 815, 300)
        rounded(canvas, box, (10, 68, 91), 24, GOLD, 5)
        title, subtitle = {
            "player": ("СОКРОВИЩА ВАШИ!", "Вы опередили пиратского соперника!"),
            "ai": ("ПИРАТ ПОБЕДИЛ!", "Соперник первым собрал четыре сокровища."),
            "draw": ("ЭКСПЕДИЦИЯ ЗАВЕРШЕНА", "Все сокровища найдены."),
        }.get(winner, ("ЭКСПЕДИЦИЯ ЗАВЕРШЕНА", "Все сокровища найдены."))
        draw_text(title, box.centerx, 425, 34, GOLD_LIGHT, True, True)
        draw_text(subtitle, box.centerx, 481, 18, WHITE, False, True)
        draw_text(f"ВАШ СЧЁТ: {player_score}     СЧЁТ ИИ: {ai_score}", box.centerx, 527, 20, GOLD_LIGHT, True, True)
        draw_text("Нажмите «НОВАЯ ЭКСПЕДИЦИЯ», чтобы сыграть ещё раз.", box.centerx, 580, 14, WHITE, False, True)

    if paused_state:
        shade = pygame.Surface((BASE_W, BASE_H), pygame.SRCALPHA)
        shade.fill((3, 31, 48, 190))
        canvas.blit(shade, (0, 0))
        box = pygame.Rect(480, 395, 630, 225)
        rounded(canvas, box, (10, 68, 91), 24, GOLD, 5)
        draw_text("ЭКСПЕДИЦИЯ НА ПАУЗЕ", box.centerx, 456, 30, GOLD_LIGHT, True, True)
        draw_text("Нажмите ESC, чтобы продолжить", box.centerx, 518, 18, WHITE, False, True)
        draw_text("F11 — полноэкранный режим", box.centerx, 556, 15, CREAM, False, True)


def draw_game(
    target_screen: pygame.Surface,
    background: pygame.Surface,
    listener: VoiceListener,
    paused_state: bool = False,
) -> None:
    mouse = screen_to_design(pygame.mouse.get_pos(), viewport_for(target_screen.get_size()))
    _draw_scene(background, listener, mouse, paused_state)
    viewport = viewport_for(target_screen.get_size())
    target_screen.fill(OCEAN)
    scaled = pygame.transform.smoothscale(canvas, viewport.size)
    target_screen.blit(scaled, viewport.topleft)
    sx, sy = viewport.width / BASE_W, viewport.height / BASE_H
    clip_before = target_screen.get_clip()
    target_screen.set_clip(viewport)
    for message, x, y, size, color, bold, center in text_commands:
        image = get_font(size, bold).render(message, True, color)
        image = pygame.transform.smoothscale(
            image,
            (
                max(1, round(image.get_width() * sx)),
                max(1, round(image.get_height() * sy)),
            ),
        )
        rect = image.get_rect()
        pixel_x, pixel_y = round(viewport.x + x * sx), round(viewport.y + y * sy)
        if center:
            rect.center = (pixel_x, pixel_y)
        else:
            rect.topleft = (pixel_x, pixel_y)
        target_screen.blit(image, rect)
    target_screen.set_clip(clip_before)
    if paused_state:
        shade = pygame.Surface(target_screen.get_size(), pygame.SRCALPHA)
        shade.fill((0, 0, 0, 70))
        target_screen.blit(shade, (0, 0))
    pygame.display.flip()


def draw_interface() -> None:
    if screen is None:
        return
    background = _load_background()
    listener = VoiceListener()
    draw_game(screen, background, listener, paused)


def _load_background() -> pygame.Surface:
    if BACKGROUND_PATH.is_file():
        try:
            return pygame.image.load(str(BACKGROUND_PATH)).convert()
        except pygame.error as exc:
            print(f"Не удалось загрузить пиратский фон: {exc}")
    fallback = pygame.Surface((BASE_W, BASE_H))
    fallback.fill(OCEAN)
    for y in range(0, BASE_H, 54):
        pygame.draw.arc(fallback, (17, 107, 137), (0, y, BASE_W, 108), 0, math.pi, 2)
    return fallback


def _start_display() -> pygame.Surface:
    pygame.init()
    pygame.display.set_caption("Пиратская охота за сокровищами")
    try:
        return pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
    except pygame.error as exc:
        print(f"Полноэкранный режим недоступен, включён оконный: {exc}")
        info = pygame.display.Info()
        return pygame.display.set_mode(
            (max(1024, info.current_w), max(680, info.current_h)),
            pygame.RESIZABLE,
        )


def _toggle_fullscreen(windowed_size: tuple[int, int]) -> tuple[pygame.Surface, tuple[int, int]]:
    global screen
    current = pygame.display.get_surface()
    if current and current.get_flags() & pygame.FULLSCREEN:
        screen = pygame.display.set_mode(windowed_size, pygame.RESIZABLE)
        return screen, windowed_size
    if current:
        windowed_size = current.get_size()
    try:
        screen = pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
    except pygame.error as exc:
        print(f"Не удалось включить полноэкранный режим: {exc}")
    return screen, windowed_size


def _process_voice_messages(listener: VoiceListener) -> None:
    global voice_status, voice_enabled, recognized_text
    while True:
        try:
            kind, text, status = listener.messages.get_nowait()
        except queue.Empty:
            break
        if kind == "status":
            voice_status = status
            if any(marker in status.lower() for marker in ("недоступен", "не установлено")):
                voice_enabled = False
        elif kind == "command":
            recognized_text = text.upper()
            handle_voice_command(text)
            if voice_enabled != listener._enabled.is_set():
                listener.set_enabled(voice_enabled)


def _click(point: tuple[float, float], listener: VoiceListener) -> None:
    global voice_enabled, paused, volume, sound_enabled, _last_sound, voice_status
    _last_sound = "click"
    if RESTART_BUTTON.collidepoint(point):
        reset_game()
        _set_captain_response("Экспедиция началась заново.")
        return
    if VOICE_BUTTON.collidepoint(point):
        voice_enabled = not voice_enabled
        listener.set_enabled(voice_enabled)
        voice_status = "МИКРОФОН: ВКЛЮЧЁН" if voice_enabled else "МИКРОФОН: ВЫКЛЮЧЕН"
        _set_captain_response("Слушаю вашу команду, капитан." if voice_enabled else "Голосовое управление выключено.")
        return
    if SOUND_BUTTON.collidepoint(point):
        sound_enabled = not sound_enabled
        if _sound_manager is not None:
            _sound_manager.set_music(sound_enabled, volume)
        return
    if VOLUME_TRACK.inflate(20, 24).collidepoint(point):
        volume = max(0.0, min(1.0, (point[0] - VOLUME_TRACK.x) / VOLUME_TRACK.width))
        if _sound_manager is not None:
            _sound_manager.set_music(sound_enabled, volume)
        return
    for mode, rect in STRATEGY_BUTTONS.items():
        if rect.collidepoint(point):
            select_strategy(mode)
            _set_captain_response(f"Стратегия {MODE_NAMES[mode]} активирована.")
            return
    if game_over or paused:
        return
    pos = cell_at(point)
    if pos is not None:
        before_score = player_score
        if do_player_move(pos):
            _set_captain_response(
                "Сундук найден! Отличная работа, капитан."
                if player_score > before_score
                else f"В клетке {coord_name(pos)} найден сигнал {str(revealed[pos]['clue']).lower()}."
            )
            _last_sound = "treasure" if player_score > before_score else "open"


def main() -> None:
    global screen, running, paused, voice_enabled, voice_status
    global _speech_output, _sound_manager, _last_sound, captain_response
    screen = _start_display()
    clock = pygame.time.Clock()
    background = _load_background()
    reset_game()
    listener = VoiceListener()
    listener.start()
    _speech_output = SpeechOutput()
    _sound_manager = SoundManager()
    if _sound_manager.error:
        captain_response = _sound_manager.error
    _sound_manager.set_music(sound_enabled, volume)
    running = True
    windowed_size = (1366, 768)
    try:
        while running:
            clock.tick(60)
            _process_voice_messages(listener)
            if _speech_output is not None and _speech_output.error:
                captain_response = _speech_output.error
            if _sound_manager is not None and _last_sound is not None:
                _sound_manager.play(_last_sound, sound_enabled, volume)
                _last_sound = None
            draw_game(screen, background, listener, paused)
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        paused = not paused
                    elif event.key == pygame.K_F11:
                        screen, windowed_size = _toggle_fullscreen(windowed_size)
                    elif event.key == pygame.K_r and not paused:
                        reset_game()
                elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                    point = screen_to_design(event.pos, viewport_for(screen.get_size()))
                    if point is not None:
                        _click(point, listener)
            if paused:
                pygame.time.wait(20)
    finally:
        voice_enabled = False
        listener.stop()
        if _speech_output is not None:
            _speech_output.stop()
        pygame.quit()


reset_game()

if __name__ == "__main__":
    main()