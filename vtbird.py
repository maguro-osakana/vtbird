#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""vtbird.py -- VT Bird, a F-Bird-style game for 80x25 VT terminals.

Usage:
    python3 vtbird.py [--truecolor|--256|--16|--no-color] [--unicode|--ascii]
    (or chmod +x and run ./vtbird.py)

Controls:
    SPACE  flap / start / continue
    C      continue (game over only)
    P      pause / resume
    R      restart
    Q      quit

Color mode and sprite set:
    --truecolor / --256 / --16 / --no-color  select the color mode
    --unicode / --ascii                      select the sprite set
    Options not given are asked at startup (no auto-detection).

Requirements: Python 3.8+, a VT-compatible terminal of at least 80x25.
Standard library only.
"""

import atexit
import fcntl
import math
import random
import select
import signal
import struct
import sys
import termios
import time
import tty

# --------------------------------------------------------------- 画面レイアウト

W, H = 80, 25          # フィールドサイズ(列, 行)
HUD_Y = 0              # HUD 行
TOP = 1                # プレイ可能な最初の行
GROUND_Y = 24          # 地面の行(ここに触れるとゲームオーバー)
BOTTOM = GROUND_Y - 1  # プレイ可能な最後の行

# ------------------------------------------- 調整パラメータ(30FPS 固定ステップ基準)

FPS = 30
FRAME = 1.0 / FPS

GRAVITY = 0.07         # 重力(行/フレーム^2)
FLAP_VY = -0.70        # フラップ初速(行/フレーム)
MAX_FALL = 1.00        # 落下速度上限(行/フレーム)

BIRD_X = 18            # 鳥の X 座標(体の左端、固定)

PIPE_SPEED0 = 0.50     # パイプ速度(列/フレーム)スコア 0 時
PIPE_SPEED_INC = 0.0075
PIPE_SPEED_MAX = 0.80
PIPE_SPACING = 20      # パイプの間隔(列)
PIPE_W = 3             # パイプの幅(列)
GAP0 = 7               # 隙間の行数(スコア 0 時)
GAP_MIN = 5
GAP_STEP = 6           # 隙間が 1 行縮むのに必要なスコア

CLOUD_SPEED = 0.15     # 雲の速度(列/フレーム、パララックス)
CLOUD_COUNT = 4        # 雲の数
POP_TTL = 20           # +1 ポップの寿命(フレーム)
FLASH_FRAMES = 6       # 死亡時フラッシュの長さ(フレーム)
CONTINUE_CLEAR = 15    # コンティニュー時に鳥の前方から取り除くパイプの距離(列)

# --------------------------------------------------------------- スプライト

SPRITES_UNICODE = {
    'bird_rise': '◓', 'bird_level': '●', 'bird_fall': '◒',
    'beak': '▸',
    'pipe': '█', 'cap_top': '▄', 'cap_bottom': '▀',
    'grass': ['▄', '▂', '▀', '▂'],
    'cloud': '☁', 'sun': '☀', 'pop': '+1',
}
SPRITES_ASCII = {
    'bird_rise': '^', 'bird_level': 'o', 'bird_fall': 'v',
    'beak': '',
    'pipe': '#', 'cap_top': '#', 'cap_bottom': '#',
    'grass': ['='],
    'cloud': '', 'sun': '', 'pop': '+1',
}

# --------------------------------------------------------------- パレット

# 行1-23 の 256 色空グラデ(紺 → シアン)
SKY_256 = [17, 17, 18, 18, 19, 19, 20, 20, 26, 26, 31, 31,
           32, 32, 38, 38, 44, 44, 45, 45, 51, 51, 51]


def build_palette(mode):
    """色モード('truecolor' / '256' / '16' / 'none')ごとの SGR パレット。"""
    if mode == 'truecolor':
        sky = []
        for y in range(1, 24):
            t = (y - 1) / 22.0
            sky.append('48;2;%d;%d;%d' % (round(8 + 102 * t),
                                          round(16 + 174 * t),
                                          round(48 + 202 * t)))
        return {
            'sky': sky,
            'flash': '48;2;120;10;10',
            'pipe': ['38;2;150;245;120', '38;2;70;190;70', '38;2;25;120;35'],
            'cap': '38;2;190;255;160',
            'bird': '1;38;2;255;215;0',
            'beak': '38;2;255;150;40',
            'cloud': '38;2;240;240;255',
            'sun': '1;38;2;255;230;120',
            'dirt': '48;2;105;70;35',
            'grass': '38;2;60;170;45',
            'hud_bg': '48;2;10;20;60',
            'hud_title': '1;38;2;255;215;0',
            'hud_val': '1;37',
            'hud_best': '1;38;2;120;220;255',
            'hud_hint': '38;2;150;150;160',
            'text': '1;37',
            'faint': '38;2;170;170;180',
            'box': '36',
            'rainbow': ['1;38;2;255;80;80', '1;38;2;255;180;40', '1;38;2;255;240;80',
                        '1;38;2;110;230;110', '1;38;2;90;170;255', '1;38;2;190;120;255'],
        }
    if mode == '256':
        return {
            'sky': ['48;5;%d' % n for n in SKY_256],
            'flash': '48;5;52',
            'pipe': ['38;5;120', '38;5;71', '38;5;22'],
            'cap': '38;5;157',
            'bird': '1;38;5;226',
            'beak': '38;5;214',
            'cloud': '1;38;5;255',
            'sun': '1;38;5;220',
            'dirt': '48;5;94',
            'grass': '38;5;28',
            'hud_bg': '48;5;24',
            'hud_title': '1;38;5;226',
            'hud_val': '1;37',
            'hud_best': '1;38;5;51',
            'hud_hint': '38;5;145',
            'text': '1;37',
            'faint': '38;5;145',
            'box': '36',
            'rainbow': ['1;38;5;196', '1;38;5;208', '1;38;5;220',
                        '1;38;5;118', '1;38;5;81', '1;38;5;213'],
        }
    if mode == '16':
        return {
            'sky': ['44'] * 23,
            'flash': '41',
            'pipe': ['1;32', '32', '32'],
            'cap': '1;32',
            'bird': '1;33',
            'beak': '33',
            'cloud': '1;37',
            'sun': '1;33',
            'dirt': '40',
            'grass': '1;32',
            'hud_bg': '44',
            'hud_title': '1;33',
            'hud_val': '1;37',
            'hud_best': '1;36',
            'hud_hint': '37',
            'text': '1;37',
            'faint': '37',
            'box': '1;36',
            'rainbow': ['1;33'],
        }
    # 'none': 色なし(--no-color)
    return {
        'sky': [''] * 23, 'flash': '', 'pipe': ['', '', ''], 'cap': '',
        'bird': '', 'beak': '', 'cloud': '', 'sun': '', 'dirt': '', 'grass': '',
        'hud_bg': '', 'hud_title': '', 'hud_val': '', 'hud_best': '', 'hud_hint': '',
        'text': '', 'faint': '', 'box': '', 'rainbow': [''],
    }


# 現在のグラフィックス設定(import 時の既定値はテストでも決定的な 256色/Unicode)
P = build_palette('256')
SPR = SPRITES_UNICODE
BIRD_W = 2  # 鳥の幅(セル)。ASCII スプライトでは 1

RESET = '\033[0m'
# DEC 2026 同期更新: この間の更新は端末が原子的に表示する(テアリング防止)。
# 未対応の端末は未知のプライベートモードとして無視するため安全。
SYNC_BEGIN = '\033[?2026;1$h'
SYNC_END = '\033[?2026;1$l'

g_running = True
old_termios = None
_cleaned = False


def init_graphics(color_mode, use_ascii):
    """起動時(またはテスト時)にパレットとスプライトを確定させる。"""
    global P, SPR, BIRD_W
    P = build_palette(color_mode)
    SPR = SPRITES_ASCII if use_ascii else SPRITES_UNICODE
    BIRD_W = 2 if SPR['beak'] else 1


# --------------------------------------------------------------- 起動時の設定入力

USAGE = """\
Usage: python3 vtbird.py [color mode] [sprite set]

  Color mode:  --truecolor  --256  --16  --no-color
  Sprite set:  --unicode  --ascii
  -h, --help   show this help

  Any option not given is asked at startup.
"""


def ask_color_mode(input_fn=input):
    """色モードを標準入力から尋ねる(引数未指定時)。"""
    while True:
        try:
            raw = input_fn('Color mode [1=truecolor / 2=256 colors / 3=16 colors'
                           ' / 4=none] (Enter=1): ')
        except EOFError:
            sys.exit('vtbird: cannot read input; '
                     'specify the mode with flags like --truecolor')
        raw = raw.strip()
        if raw in ('', '1'):
            return 'truecolor'
        if raw == '2':
            return '256'
        if raw == '3':
            return '16'
        if raw == '4':
            return 'none'
        print('Please enter 1-4')


def ask_use_ascii(input_fn=input):
    """文字スプライト(Unicode/ASCII)を標準入力から尋ねる(引数未指定時)。"""
    while True:
        try:
            raw = input_fn('Sprite set [1=Unicode / 2=ASCII] (Enter=1): ')
        except EOFError:
            sys.exit('vtbird: cannot read input; '
                     'specify --unicode or --ascii')
        raw = raw.strip()
        if raw in ('', '1'):
            return False
        if raw == '2':
            return True
        print('Please enter 1 or 2')


def parse_args(argv):
    """コマンドライン引数を解析する。指定がない項目は None のまま返す。"""
    flags = {'color': None, 'ascii': None}
    for a in argv:
        if a == '--truecolor':
            flags['color'] = 'truecolor'
        elif a == '--256':
            flags['color'] = '256'
        elif a == '--16':
            flags['color'] = '16'
        elif a == '--no-color':
            flags['color'] = 'none'
        elif a == '--unicode':
            flags['ascii'] = False
        elif a == '--ascii':
            flags['ascii'] = True
        elif a in ('-h', '--help'):
            print(USAGE)
            sys.exit(0)
        else:
            sys.exit('vtbird: unknown argument: %s\n%s' % (a, USAGE))
    return flags


# --------------------------------------------------------------- ゲーム状態

class Game:
    __slots__ = ('state', 'bird_y', 'bird_vy', 'pipes', 'score', 'best',
                 'clouds', 'pops', 'over_t')

    def __init__(self):
        self.state = 'title'
        self.best = 0
        self.reset()

    def reset(self):
        self.bird_y = (TOP + BOTTOM) / 2.0
        self.bird_vy = 0.0
        self.pipes = []
        self.pops = []
        self.over_t = 0
        self.score = 0
        # 雲: 1 つは画面内、残りは右側の画面外から流入
        self.clouds = [{'x': random.uniform(4, 70), 'y': random.randint(2, 8)}]
        self.clouds += [{'x': float(W) + random.uniform(5, 60),
                         'y': random.randint(2, 8)} for _ in range(CLOUD_COUNT - 1)]


def pipe_speed(score):
    """難易度漸増: スコアに応じてパイプが速くなる。"""
    return min(PIPE_SPEED0 + score * PIPE_SPEED_INC, PIPE_SPEED_MAX)


def gap_for(score):
    """難易度漸増: スコアに応じて隙間が狭くなる。"""
    return max(GAP_MIN, GAP0 - score // GAP_STEP)


def update(g):
    # 雲をゆっくり流し、画面外に出たら右から再投入
    for c in g.clouds:
        c['x'] -= CLOUD_SPEED
        if c['x'] < -2:
            c['x'] = W + random.uniform(5, 40)
            c['y'] = random.randint(2, 8)

    g.bird_vy = min(g.bird_vy + GRAVITY, MAX_FALL)
    g.bird_y += g.bird_vy
    if g.bird_y < TOP:  # 天井はクランプ(死なない)
        g.bird_y = TOP
        g.bird_vy = max(g.bird_vy, 0.0)

    speed = pipe_speed(g.score)
    for p in g.pipes:
        p['x'] -= speed

    # 新しいパイプを右端の外に生成
    if not g.pipes or g.pipes[-1]['x'] < W - PIPE_SPACING:
        gap = gap_for(g.score)
        g.pipes.append({
            'x': float(W),
            'gap_top': random.randint(TOP, BOTTOM - gap),
            'gap': gap,
            'passed': False,
        })
    if g.pipes and g.pipes[0]['x'] + PIPE_W <= 0:
        g.pipes.pop(0)

    bird_row = round(g.bird_y)
    bird_right = BIRD_X + BIRD_W - 1
    if bird_row >= GROUND_Y:  # 地面
        die(g)
        return
    for p in g.pipes:
        px = int(p['x'])
        if px <= bird_right and px + PIPE_W - 1 >= BIRD_X and not (
            p['gap_top'] <= bird_row <= p['gap_top'] + p['gap'] - 1
        ):
            die(g)
            return
        if not p['passed'] and p['x'] + PIPE_W < BIRD_X:  # 通過でスコア
            p['passed'] = True
            g.score += 1
            g.pops.append({'x': float(BIRD_X), 'y': float(bird_row - 1),
                           'ttl': POP_TTL})

    # +1 ポップは左上へ漂って消える
    for pop in g.pops:
        pop['x'] -= 0.2
        pop['y'] -= 0.12
        pop['ttl'] -= 1
    g.pops = [p for p in g.pops if p['ttl'] > 0]


def die(g):
    if g.score > g.best:
        g.best = g.score
    g.state = 'over'
    g.over_t = 0
    sys.stdout.write('\a')


def continue_game(g):
    """ゲームオーバーの場面から再開する(スコアとパイプは維持)。

    鳥を中央に戻し、すぐ前方のパイプを取り除くことで即死を防ぐ。
    完全に通過済みのパイプと、十分先方のパイプはそのまま残す。
    """
    g.bird_y = (TOP + BOTTOM) / 2.0
    g.bird_vy = 0.0
    g.pops = []
    g.pipes = [p for p in g.pipes
               if p['x'] + PIPE_W <= BIRD_X
               or p['x'] >= BIRD_X + BIRD_W + CONTINUE_CLEAR]


# --------------------------------------------------------------- 描画

def join_sgr(fg, bg):
    """前景 SGR と背景 SGR を 1 つのパラメータ文字列に結合する。"""
    if fg and bg:
        return fg + ';' + bg
    return fg or bg


def bg_at(y, flashing=False):
    """行 y の背景色(空グラデ / HUD バー / 土 / 死亡フラッシュ)。"""
    if y == HUD_Y:
        return P['hud_bg']
    if y == GROUND_Y:
        return P['dirt']
    if TOP <= y < GROUND_Y:
        return P['flash'] if flashing else P['sky'][y - 1]
    return ''


def blank_grid(flashing=False):
    return [[(' ', bg_at(y, flashing))] * W for y in range(H)]


def put_text(grid, x, y, text, fg, flashing=False):
    if not 0 <= y < H:
        return
    sgr = join_sgr(fg, bg_at(y, flashing))
    for i, ch in enumerate(text):
        if 0 <= x + i < W:
            grid[y][x + i] = (ch, sgr)


def draw_sun(grid):
    if SPR['sun']:
        grid[2][72] = (SPR['sun'], join_sgr(P['sun'], bg_at(2)))


def draw_clouds(grid, clouds):
    ch = SPR['cloud']
    if not ch:
        return
    for c in clouds:
        x, y = int(round(c['x'])), c['y']
        if 0 <= x < W and TOP <= y < GROUND_Y:
            grid[y][x] = (ch, join_sgr(P['cloud'], bg_at(y)))


def draw_pipes(grid, pipes, flashing=False):
    for p in pipes:
        x0 = int(p['x'])
        # 本体: 左列ほど明るい(円筒の陰影)
        for i in range(PIPE_W):
            x = x0 + i
            if not 0 <= x < W:
                continue
            fg = P['pipe'][min(i, len(P['pipe']) - 1)]
            for y in range(TOP, p['gap_top']):
                grid[y][x] = (SPR['pipe'], join_sgr(fg, bg_at(y, flashing)))
            for y in range(p['gap_top'] + p['gap'], GROUND_Y):
                grid[y][x] = (SPR['pipe'], join_sgr(fg, bg_at(y, flashing)))
    # 隙間の縁にキャップ(Unicode のみ)
    if SPR['cap_top'] != SPR['pipe']:
        for p in pipes:
            x0 = int(p['x'])
            cap_y = p['gap_top'] - 1
            if TOP <= cap_y < GROUND_Y:
                for i in range(PIPE_W):
                    x = x0 + i
                    if 0 <= x < W:
                        grid[cap_y][x] = (SPR['cap_top'],
                                          join_sgr(P['cap'], bg_at(cap_y, flashing)))
            cap_y = p['gap_top'] + p['gap']
            if TOP <= cap_y < GROUND_Y:
                for i in range(PIPE_W):
                    x = x0 + i
                    if 0 <= x < W:
                        grid[cap_y][x] = (SPR['cap_bottom'],
                                          join_sgr(P['cap'], bg_at(cap_y, flashing)))


def draw_pops(grid, pops):
    if SPR['pop']:
        for p in pops:
            put_text(grid, int(round(p['x'])), int(round(p['y'])), SPR['pop'], P['bird'])


def draw_ground(grid):
    pat = SPR['grass']
    for x in range(W):
        grid[GROUND_Y][x] = (pat[x % len(pat)], join_sgr(P['grass'], P['dirt']))


def draw_bird(grid, y, vy, flashing=False):
    row = int(round(y))
    if not 0 <= row < H:
        return
    if vy < -0.15:
        ch = SPR['bird_rise']
    elif vy > 0.35:
        ch = SPR['bird_fall']
    else:
        ch = SPR['bird_level']
    bg = bg_at(row, flashing)
    grid[row][BIRD_X] = (ch, join_sgr(P['bird'], bg))
    if SPR['beak'] and BIRD_X + 1 < W:
        grid[row][BIRD_X + 1] = (SPR['beak'], join_sgr(P['beak'], bg))


def draw_hud(grid, g):
    put_text(grid, 1, HUD_Y, 'VT BIRD', P['hud_title'])
    put_text(grid, 25, HUD_Y, 'SCORE %04d' % g.score, P['hud_val'])
    put_text(grid, 40, HUD_Y, 'BEST %04d' % g.best, P['hud_best'])
    if g.state == 'play':
        put_text(grid, 56, HUD_Y, 'P:PAUSE  Q:QUIT', P['hud_hint'])
    else:
        put_text(grid, 56, HUD_Y, 'Q:QUIT', P['hud_hint'])


TITLE = 'VT BIRD'
TITLE_Y = 3   # タイトルアートの開始行
DUCK_Y = 9    # マスコットの開始行
TITLE_ART = {
    'V': ['#   #', '#   #', '#   #', ' # # ', '  #  '],
    'T': ['#####', '  #  ', '  #  ', '  #  ', '  #  '],
    'B': ['#### ', '#   #', '#### ', '#   #', '#### '],
    'I': ['###', ' # ', ' # ', ' # ', '###'],
    'R': ['#### ', '#   #', '#### ', '#  # ', '#   #'],
    'D': ['### ', '#  #', '#  #', '#  #', '### '],
}
DUCK_ART = (
    '   __',
    ' <(o )___',
    '  ( ._> /',
    "   `---'",
)


def draw_title(grid):
    """タイトル画面: ASCII アートロゴ(VT BIRD)とマスコットのアヒル。"""
    # ロゴ全体の幅を算出(文字間 1 列、単語間 3 列)
    art_w = sum(3 if c == ' ' else len(TITLE_ART[c][0]) + 1 for c in TITLE) - 1
    x0 = (W - art_w) // 2
    rainbow = P['rainbow']
    x, li = x0, 0
    for c in TITLE:
        if c == ' ':
            x += 3
            continue
        letter = TITLE_ART[c]
        for r, line in enumerate(letter):
            for j, ch in enumerate(line):
                if ch == '#':  # 1 文字ずつ虹色に
                    put_text(grid, x + j, TITLE_Y + r, '#',
                             rainbow[li % len(rainbow)])
        x += len(letter[0]) + 1
        li += 1
    # マスコットのアヒル
    for r, line in enumerate(DUCK_ART):
        put_text(grid, (W - 9) // 2, DUCK_Y + r, line, P['bird'])
    put_text(grid, (W - 22) // 2, 14, 'PRESS [SPACE] TO START', P['text'])
    put_text(grid, (W - 16) // 2, 16, 'P:PAUSE   Q:QUIT', P['faint'])


def draw_over_box(grid, g, flashing=False):
    inner = 32
    x0 = (W - inner - 2) // 2
    y0 = 8
    rows = [
        ('┌' + '─' * inner + '┐', P['box']),
        ('│' + 'GAME OVER'.center(inner) + '│', P['text']),
        ('│' + ' ' * inner + '│', P['box']),
        ('│' + ('SCORE %04d     BEST %04d' % (g.score, g.best)).center(inner) + '│',
         P['hud_val']),
        ('│' + ' ' * inner + '│', P['box']),
        ('│' + '[SPACE] / [C] : CONTINUE'.center(inner) + '│', P['bird']),
        ('│' + '[R] RETRY       [Q] QUIT'.center(inner) + '│', P['text']),
        ('└' + '─' * inner + '┘', P['box']),
    ]
    for i, (text, fg) in enumerate(rows):
        put_text(grid, x0, y0 + i, text, fg, flashing)


def draw_pause_box(grid):
    inner = 16
    x0 = (W - inner - 2) // 2
    y0 = 10
    rows = [
        ('┌' + '─' * inner + '┐', P['box']),
        ('│' + 'PAUSED'.center(inner) + '│', P['text']),
        ('│' + '[P] RESUME'.center(inner) + '│', P['hud_val']),
        ('└' + '─' * inner + '┘', P['box']),
    ]
    for i, (text, fg) in enumerate(rows):
        put_text(grid, x0, y0 + i, text, fg)


def grid_text(grid):
    """テスト用: 色なしプレーンテキストに変換。"""
    return '\n'.join(''.join(ch for ch, _ in row) for row in grid)


def row_text(row):
    parts = []
    last = ''
    for ch, color in row:
        if color != last:
            parts.append('\033[%sm' % color if color else RESET)
            last = color
        parts.append(ch)
    if last:
        parts.append(RESET)
    return ''.join(parts)


def render(g, frame):
    flashing = g.state == 'over' and g.over_t < FLASH_FRAMES
    grid = blank_grid(flashing)
    draw_sun(grid)
    draw_clouds(grid, g.clouds)
    draw_pipes(grid, g.pipes, flashing)
    draw_pops(grid, g.pops)
    draw_ground(grid)
    if g.state == 'title':
        # タイトル画面では鳥が上下にゆれている(演出)
        draw_bird(grid, (TOP + BOTTOM) / 2 + math.sin(frame / 8.0) * 2.0, 0.0)
        draw_title(grid)
    else:
        draw_bird(grid, g.bird_y, g.bird_vy, flashing)
        if g.state == 'pause':
            draw_pause_box(grid)
        elif g.state == 'over':
            draw_over_box(grid, g, flashing)
    draw_hud(grid, g)
    flush_frame(grid)


_last_grid = None  # 前フレームのグリッド(セル差分計算用)
_last_sgr = ''     # 端末に最後に送った SGR('' = 既定色)


def reset_diff():
    """次の flush_frame をフル再描画にする(ゲーム開始・リトライ時の自己修復)。"""
    global _last_grid
    _last_grid = None


def flush_frame(grid):
    """1 フレームを出力する。

    初回は全面を描き、以降は前フレームと異なるセルだけを送る(セル差分)。
    フレームは常に 4KB 未満になり単一チャンクで端末に届くため、
    DEC 2026 同期更新と併せてテアリング(画面中央の割れ)を防止する。
    """
    global _last_grid, _last_sgr
    body = []
    if _last_grid is None:
        # フルフレーム: 各行を配置して描く。
        # row_text は色付き行の末尾で RESET するため、送出後の端末の色状態は既定色
        for y in range(H):
            body.append('\033[%d;1H' % (y + 1))
            body.append(row_text(grid[y]))
        _last_sgr = ''
    else:
        # 差分フレーム: 変化したセルの横連続ランだけを送る
        for y in range(H):
            row, last = grid[y], _last_grid[y]
            x = 0
            while x < W:
                if row[x] == last[x]:
                    x += 1
                    continue
                x0 = x
                while x < W and row[x] != last[x]:
                    x += 1
                body.append('\033[%d;%dH' % (y + 1, x0 + 1))
                for cx in range(x0, x):
                    ch, sgr = row[cx]
                    if sgr != _last_sgr:
                        body.append('\033[%sm' % sgr if sgr else RESET)
                        _last_sgr = sgr
                    body.append(ch)
    _last_grid = [list(r) for r in grid]
    if not body:
        return  # 変化なし: 出力しない
    sys.stdout.write(''.join([SYNC_BEGIN] + body + [SYNC_END]))
    sys.stdout.flush()


# --------------------------------------------------------------- 端末の setup / cleanup

def term_size():
    try:
        packed = fcntl.ioctl(sys.stdout.fileno(), termios.TIOCGWINSZ, b'\x00' * 8)
        rows, cols = struct.unpack('hh', packed[:4])
        return cols, rows
    except OSError:
        return 0, 0


def setup():
    global old_termios
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        sys.exit('vtbird: must be run from a TTY')
    cols, rows = term_size()
    if cols < W or rows < H:
        sys.exit('vtbird: terminal must be at least %dx%d (got %dx%d)'
                 % (W, H, cols, rows))
    old_termios = termios.tcgetattr(sys.stdin)
    tty.setcbreak(sys.stdin.fileno())
    atexit.register(cleanup)
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, _on_signal)
    # 代替スクリーンに入り、カーソルを隠す
    sys.stdout.write('\033[?1049h\033[?25l\033[2J')
    sys.stdout.flush()


def _on_signal(signum, frame):
    global g_running
    g_running = False


def cleanup():
    """端末状態を必ず復元する(atexit / シグナル経由で呼ばれる)。"""
    global _cleaned
    if _cleaned or old_termios is None:
        return
    _cleaned = True
    sys.stdout.write(RESET + '\033[?25h\033[?1049l')
    sys.stdout.flush()
    termios.tcsetattr(sys.stdin, termios.TCSADRAIN, old_termios)


# --------------------------------------------------------------- 入力

def read_keys():
    global g_running
    keys = []
    while select.select([sys.stdin], [], [], 0)[0]:
        ch = sys.stdin.read(1)
        if not ch:  # EOF
            g_running = False
            break
        keys.append(ch)
    return keys


def handle_key(g, ch):
    global g_running
    if ch in 'qQ':
        g_running = False
    elif ch in ' \r\n':
        if g.state == 'title':
            g.reset()
            g.state = 'play'
            reset_diff()  # 開始時はフル再描画
        elif g.state == 'play':
            g.bird_vy = FLAP_VY
        elif g.state == 'over':
            continue_game(g)
            g.state = 'play'
            reset_diff()  # 場面が大きく変わるためフル再描画
    elif ch in 'cC':
        if g.state == 'over':
            continue_game(g)
            g.state = 'play'
            reset_diff()
    elif ch in 'pP':
        if g.state == 'play':
            g.state = 'pause'
        elif g.state == 'pause':
            g.state = 'play'
    elif ch in 'rR':
        if g.state != 'title':
            g.reset()
            g.state = 'play'
            reset_diff()


# --------------------------------------------------------------- メインループ

def main():
    flags = parse_args(sys.argv[1:])
    color_mode = flags['color']
    use_ascii = flags['ascii']
    if color_mode is None or use_ascii is None:
        # 引数で指定されていない項目だけ、起動時に尋ねる
        print('VT BIRD - terminal setup')
        print('(pass flags like --truecolor --unicode to skip these'
              ' questions next time)')
        if color_mode is None:
            color_mode = ask_color_mode()
        if use_ascii is None:
            use_ascii = ask_use_ascii()
    init_graphics(color_mode, use_ascii)
    setup()
    reset_diff()  # 初回はフル再描画
    g = Game()
    frame = 0
    next_tick = time.monotonic()
    while g_running:
        delay = next_tick - time.monotonic()
        if delay > 0:
            # フレーム待ちとキー待ちを同じ select に統合(入力で早期復帰)
            select.select([sys.stdin], [], [], delay)
        if delay < -0.5:  # サスペンド明けなど: クロックを再同期
            next_tick = time.monotonic()
        for ch in read_keys():
            handle_key(g, ch)
        if g_running and g.state == 'play':
            update(g)
        if g_running:
            render(g, frame)
            frame += 1
        if g.state == 'over':
            g.over_t += 1
        next_tick += FRAME


if __name__ == '__main__':
    try:
        main()
    finally:
        cleanup()
