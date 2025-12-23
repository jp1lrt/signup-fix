# main.py
# コンテスト集計チェッカー（単体 main.py）
# - フォルダ内の *.log / *.txt / *.adi / *.dat など（テキストとして読めるもの）を一括読込
# - 画面上にサマリー＋ログの塊を貼り付けて追加も可能
# - 右クリック「貼り付け」などのコンテキストメニューあり
# - 「貼り付け内容を追加」成功時に入力欄を自動クリア（貼り付け/コール/運用地）
# - MULT は「受信ナンバー（RCVD Exchange）」のユニーク数で再計算（ログの Mlt 列に依存しない）
# - DUP は（BAND, MODE, 相手CALL）で二重交信を判定し 0点扱い＋マルチにも入れない
# - 申告点が 0 の場合は“差なし扱い”（要望：0申告は訂正せず 0 のまま扱う）
# - ★追加: 手動訂正（局ごとに再計算値を上書き）＋JSON保存（manual_overrides.json）
# - ★追加: 運用地も手動上書き＆JSON保存（manual_opplace）
# - ★追加: 運用地の表示ルール（強制正規化）
# - ★追加: LOG保存(CTESTWIN化)
# - ★追加: 発表HTML出力（部門別+総合+コメント）
# - ★追加: 賞状/参加証 PDF 出力（ReportLab） ※今回ここを強化（位置/サイズ調整）

from __future__ import annotations

import os
import re
import csv
import glob
import json
import html
import traceback
from dataclasses import dataclass, field
from typing import List, Optional, Dict, Tuple, Any

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# ★追加: PDF生成（賞状/参加証）
from datetime import datetime
from reportlab.pdfgen import canvas as rl_canvas
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.cidfonts import UnicodeCIDFont
from reportlab.lib.utils import ImageReader


# -----------------------------
# Settings (Contest / Display)
# -----------------------------

CONTEST_TITLE = "第41回 1エリアAMコンテスト"
CONTEST_YEAR = 2025  # 西暦
ORGANIZER_NAME = "6mコンテストグループ まんなかくらぶ"

# 主催者（JP1LRT）をチェックログ扱いにして表彰・参加証から除外したい
CHECKLOG_CALLSIGNS = {""}  # 必要なら増やせます

# 部門コードの表示名（表示統一：1Qは「QRP局」、SWLは「SWL」）
CATEGORY_LABELS = {
    "1F": "1エリア内固定局",
    "1P": "1エリア内移動局",
    "1X": "1エリア外局",
    "1Q": "QRP局",
    "SWL": "SWL",  # "SWL SWL" ではなく "SWL" と表示されるように
}


# 賞状本文（コールサインだけでOK）
AWARD_SENTENCE = f"{CONTEST_TITLE}において優秀なる成績を収められましたのでこれを賞します"

# PDF背景ファイル名（集計フォルダに置く）
DEFAULT_CERT_BG = "certificate_bg.png"  # 賞状
DEFAULT_ENTRY_BG = "entry_bg.png"       # 参加証


# -----------------------------
# Data models
# -----------------------------

@dataclass
class QsoRecord:
    date: str = ""
    time: str = ""
    band_mhz: str = ""
    mode: str = ""
    worked_call: str = ""
    sent_exch: str = ""
    rcvd_exch: str = ""
    pts: int = 0
    dup: bool = False
    raw: str = ""


@dataclass
class StationEntry:
    callsign: str = ""
    category: str = ""
    category_name: str = ""
    opplace: str = ""     # 運用地（表示用）
    address: str = ""
    comments: str = ""
    logsheet_type: str = ""
    claimed_qso: Optional[int] = None
    claimed_pts: Optional[int] = None
    claimed_mult: Optional[int] = None
    claimed_total: Optional[int] = None

    qsos: List[QsoRecord] = field(default_factory=list)

    recalced_qso: int = 0
    recalced_pts: int = 0
    recalced_mult: int = 0
    recalced_total: int = 0

    # ★手動訂正（再計算値の上書き）
    manual_enabled: bool = False
    manual_qso: Optional[int] = None
    manual_pts: Optional[int] = None
    manual_mult: Optional[int] = None
    manual_total: Optional[int] = None
    manual_note: str = ""

    # ★運用地の手動上書き（manual_enabled が True の時だけ反映）
    manual_opplace: str = ""

    match: bool = True
    reason: str = ""
    source_name: str = ""          # ファイル名等（任意）
    raw_submission_text: str = ""  # ★元提出テキスト保持

    # ★追加: チェックログ判定
    is_checklog: bool = False


# -----------------------------
# Utility: normalize / parsing helpers
# -----------------------------

RST_PREFIXES = ("59", "57", "55", "58", "56")

PREFS = [
    "東京都", "北海道", "大阪府", "京都府",
    "青森県", "岩手県", "宮城県", "秋田県", "山形県", "福島県",
    "茨城県", "栃木県", "群馬県", "埼玉県", "千葉県", "神奈川県",
    "新潟県", "富山県", "石川県", "福井県", "山梨県", "長野県",
    "岐阜県", "静岡県", "愛知県", "三重県",
    "滋賀県", "兵庫県", "奈良県", "和歌山県",
    "鳥取県", "島根県", "岡山県", "広島県", "山口県",
    "徳島県", "香川県", "愛媛県", "高知県",
    "福岡県", "佐賀県", "長崎県", "熊本県", "大分県", "宮崎県", "鹿児島県", "沖縄県",
]

HYPHEN_CHARS = r"[\-‐-‒–—―−ー－]"
HOME_MARKERS = ("常置場所", "同上", "自宅", "住所", "自局")


def _clean(s: str) -> str:
    return (s or "").replace("\r\n", "\n").replace("\r", "\n")

def _strip_tags_text(x: str) -> str:
    return re.sub(r"[ \t]+", " ", (x or "").strip()).strip()

def _find_tag(text: str, tag: str) -> Optional[str]:
    m = re.search(rf"<{re.escape(tag)}>(.*?)</{re.escape(tag)}>", text, flags=re.DOTALL | re.IGNORECASE)
    if not m:
        return None
    return _strip_tags_text(m.group(1))

def _find_attr(text: str, tag: str, attr: str) -> Optional[str]:
    m = re.search(rf"<{re.escape(tag)}\b([^>]*)>", text, flags=re.IGNORECASE)
    if not m:
        return None
    attrs = m.group(1)
    m2 = re.search(rf'{re.escape(attr)}\s*=\s*(".*?"|\'.*?\'|[^\s>]+)', attrs, flags=re.IGNORECASE)
    if not m2:
        return None
    v = m2.group(1).strip()
    if (v.startswith('"') and v.endswith('"')) or (v.startswith("'") and v.endswith("'")):
        v = v[1:-1]
    return v.strip()

def _parse_score_triplet(score_text: str) -> Tuple[Optional[int], Optional[int], Optional[int]]:
    if not score_text:
        return (None, None, None)
    parts = [p.strip() for p in score_text.split(",")]
    if len(parts) < 3:
        return (None, None, None)

    def _to_int(x: str) -> Optional[int]:
        x = x.replace(",", "").strip()
        if x == "" or x == "-":
            return None
        try:
            return int(x)
        except:
            return None

    return (_to_int(parts[0]), _to_int(parts[1]), _to_int(parts[2]))

def _safe_int(x: Any, default: int = 0) -> int:
    try:
        if x is None:
            return default
        if isinstance(x, int):
            return x
        s = str(x).strip().replace(",", "")
        if s == "" or s == "-":
            return default
        return int(s)
    except:
        return default

def _canon_exchange(exch: str) -> str:
    if exch is None:
        return ""
    s = str(exch).strip()
    if s in ("", "-"):
        return ""
    s = re.sub(r"[^\d]", "", s)
    if s == "":
        return ""
    try:
        return str(int(s))
    except:
        return s

def _extract_exchange_from_token(tok: str) -> str:
    if tok is None:
        return ""
    s = str(tok).strip()
    if s == "" or s == "-":
        return ""
    if s in RST_PREFIXES:
        return ""
    for rst in RST_PREFIXES:
        if s.startswith(rst) and len(s) > len(rst):
            tail = s[len(rst):]
            tail = re.sub(r"[^\d]", "", tail)
            return tail
    s = re.sub(r"[^\d]", "", s)
    return s

def _parse_band_mhz(tok: str) -> str:
    if tok is None:
        return ""
    s = str(tok).strip()
    s = s.replace("MHz", "").replace("mhz", "").strip()
    return s

def _canon_band_token(tok: str) -> str:
    s = _parse_band_mhz(tok).strip()
    if s == "":
        return ""
    if re.fullmatch(r"\d+(\.\d+)?", s):
        try:
            f = float(s)
            if abs(f - round(f)) < 1e-9:
                return str(int(round(f)))
            return s
        except:
            return s
    return s

def _parse_time(tok: str) -> str:
    if not tok:
        return ""
    s = str(tok).strip()
    if re.fullmatch(r"\d{2}:\d{2}", s):
        return s
    if re.fullmatch(r"\d{4}", s):
        return s[:2] + ":" + s[2:]
    return s

def _looks_date(s: str) -> bool:
    return bool(re.fullmatch(r"\d{4}[-/]\d{2}[-/]\d{2}", (s or "").strip()))

def _looks_time(s: str) -> bool:
    s = (s or "").strip()
    return bool(re.fullmatch(r"\d{2}:\d{2}", s) or re.fullmatch(r"\d{4}", s))

def _clean_callsign(call: str) -> str:
    if not call:
        return ""
    return call.strip().upper()

def _looks_callsign(tok: str) -> bool:
    s = (tok or "").strip().upper()
    if not s:
        return False
    if not re.fullmatch(r"[A-Z0-9/]+", s):
        return False
    return bool(re.search(r"[A-Z]", s))


# -----------------------------
# OPPLACE normalization (強化版)
# -----------------------------

def _opplace_means_home(opplace_raw: str) -> bool:
    t = (opplace_raw or "").strip()
    if not t:
        return True
    return any(k in t for k in HOME_MARKERS)

def _strip_postal_and_prefs(s: str) -> str:
    s = (s or "").strip()
    if not s:
        return ""
    s = re.sub(rf"〒\s*\d{{3}}\s*{HYPHEN_CHARS}\s*\d{{4}}\s*", " ", s)
    s = re.sub(r"〒\s*\d{3}\s*\d{4}\s*", " ", s)
    s = re.sub(rf"\b\d{{3}}\s*{HYPHEN_CHARS}\s*\d{{4}}\b", " ", s)
    s = re.sub(r"\b\d{3}\s*\d{4}\b", " ", s)
    for p in PREFS:
        s = s.replace(p, " ")
    s = re.sub(r"[ \t]+", " ", s).strip()
    return s

def normalize_opplace_any(text: str, fallback_text: str = "") -> str:
    s = _strip_postal_and_prefs(text)
    if not s:
        return ""

    m = re.match(r"^(.+?市.+?区)", s)
    if m:
        return m.group(1).strip()

    m = re.match(r"^(.{2,}?市)", s)
    if m:
        city = m.group(1).strip()
        if city == "さいたま市":
            m2 = re.match(r"^(さいたま市.+?区)", s)
            if m2:
                return m2.group(1).strip()
            fb = _strip_postal_and_prefs(fallback_text)
            m3 = re.search(r"(さいたま市.+?区)", fb)
            if m3:
                return m3.group(1).strip()
            return "さいたま市（区不明）"
        return city

    m = re.match(r"^(.{2,}?区)", s)
    if m:
        return m.group(1).strip()

    m = re.match(r"^.*?郡(.{1,}?町)", s)
    if m:
        return m.group(1).strip()
    m = re.match(r"^.*?郡(.{1,}?村)", s)
    if m:
        return m.group(1).strip()

    m = re.match(r"^(.{2,}?町)", s)
    if m:
        return m.group(1).strip()

    m = re.match(r"^(.{2,}?村)", s)
    if m:
        return m.group(1).strip()

    return s.strip()


# -----------------------------
# LOGSHEET parsers
# -----------------------------

def _take_pts_from_tail(tokens: List[str], raw_line: str) -> Tuple[int, List[str]]:
    if not tokens:
        return (2, tokens)
    tail = tokens[-1].replace(",", "").strip()
    if re.fullmatch(r"\d+", tail):
        return (int(tail), tokens[:-1])

    if len(tokens) >= 2 and tokens[-1].lower() in ("dupe", "dup"):
        tail2 = tokens[-2].replace(",", "").strip()
        if re.fullmatch(r"\d+", tail2):
            return (int(tail2), tokens[:-2])

    if re.search(r"\s0\s*$", raw_line):
        return (0, tokens)

    return (2, tokens)

def parse_logsheet_ctestwin(lines: List[str]) -> List[QsoRecord]:
    out: List[QsoRecord] = []
    for raw in lines:
        s = raw.strip()
        if not s:
            continue
        if s.startswith("DATE") or s.startswith("---") or s.startswith("Date"):
            continue

        parts = s.split()
        if len(parts) < 6:
            continue
        if not _looks_date(parts[0]) or not _looks_time(parts[1]):
            continue

        date = parts[0].replace("/", "-")
        time = _parse_time(parts[1])
        band = _parse_band_mhz(parts[2])

        mode_tok = parts[3]
        if mode_tok.isdigit() and len(parts) >= 6 and _looks_callsign(parts[4]):
            mode = "AM"
            call = _clean_callsign(parts[4])
            rest = parts[5:]
        else:
            mode = parts[3]
            call = _clean_callsign(parts[4])
            rest = parts[5:]

        pts, rest2 = _take_pts_from_tail(rest, s)
        rest = rest2

        sent_exch = ""
        rcvd_exch = ""

        rst_idxs = [i for i, tok in enumerate(rest) if tok in RST_PREFIXES]

        if len(rst_idxs) >= 2:
            i1, i2 = rst_idxs[0], rst_idxs[1]
            if i1 + 1 < len(rest):
                sent_exch = rest[i1 + 1]
            if i2 + 1 < len(rest):
                rcvd_exch = rest[i2 + 1]
        elif len(rst_idxs) == 1:
            i = rst_idxs[0]
            if i - 1 >= 0:
                sent_exch = rest[i - 1]
            if i + 1 < len(rest):
                rcvd_exch = rest[i + 1]
        else:
            if len(rest) >= 1:
                sent_exch = rest[0]
            if len(rest) >= 2:
                rcvd_exch = rest[1]

        sent_exch_num = _extract_exchange_from_token(sent_exch)
        rcvd_exch_num = _extract_exchange_from_token(rcvd_exch)

        sent_exch = _canon_exchange(sent_exch_num)
        rcvd_exch = _canon_exchange(rcvd_exch_num)

        if pts <= 0:
            if re.search(r"\s0\s*$", s) or "dupe" in s.lower() or "dup" in s.lower():
                pts = 0
            else:
                pts = 2

        out.append(QsoRecord(
            date=date, time=time, band_mhz=band, mode=mode,
            worked_call=call, sent_exch=sent_exch, rcvd_exch=rcvd_exch,
            pts=pts, dup=False, raw=raw
        ))
    return out

def parse_logsheet_hltst(lines: List[str]) -> List[QsoRecord]:
    out: List[QsoRecord] = []
    for raw in lines:
        s = raw.strip()
        if not s:
            continue
        if s.startswith("DATE") or s.startswith("---"):
            continue
        parts = s.split()
        if len(parts) < 10:
            continue
        if not _looks_date(parts[0]) or not _looks_time(parts[1]):
            continue
        date = parts[0].replace("/", "-")
        time = _parse_time(parts[1])
        band = _parse_band_mhz(parts[2])

        mode_tok = parts[3]
        if mode_tok.isdigit() and _looks_callsign(parts[4]):
            mode = "AM"
            call = _clean_callsign(parts[4])
            base = 5
        else:
            mode = parts[3]
            call = _clean_callsign(parts[4])
            base = 5

        sent_exch = _canon_exchange(_extract_exchange_from_token(parts[base+1])) if len(parts) > base+1 else ""
        rcvd_exch = _canon_exchange(_extract_exchange_from_token(parts[base+3])) if len(parts) > base+3 else ""

        pt = 0
        if len(parts) > base+5:
            pt = _safe_int(parts[base+5], 0)
        else:
            pt = _safe_int(parts[-1], 0)

        if pt <= 0:
            if re.search(r"\s0\s*$", s):
                pt = 0
            else:
                pt = 2

        out.append(QsoRecord(
            date=date, time=time, band_mhz=band, mode=mode,
            worked_call=call, sent_exch=sent_exch, rcvd_exch=rcvd_exch,
            pts=pt, dup=False, raw=raw
        ))
    return out

def parse_logsheet_zlog(lines: List[str]) -> List[QsoRecord]:
    out: List[QsoRecord] = []
    for raw in lines:
        s = raw.strip()
        if not s:
            continue
        if s.lower().startswith("date") or s.startswith("---"):
            continue
        parts = s.split()
        if len(parts) < 12:
            continue
        if not _looks_date(parts[0]) or not _looks_time(parts[1]):
            continue
        date = parts[0].replace("/", "-")
        time = _parse_time(parts[1])
        call = _clean_callsign(parts[2])

        sent_exch = _canon_exchange(_extract_exchange_from_token(parts[4]))
        rcvd_exch = _canon_exchange(_extract_exchange_from_token(parts[6]))
        band = _parse_band_mhz(parts[9])
        mode = parts[10]
        pt = _safe_int(parts[11], 0)
        if pt <= 0:
            if re.search(r"\s0\s*$", s):
                pt = 0
            else:
                pt = 2

        out.append(QsoRecord(
            date=date, time=time, band_mhz=band, mode=mode,
            worked_call=call, sent_exch=sent_exch, rcvd_exch=rcvd_exch,
            pts=pt, dup=False, raw=raw
        ))
    return out

def parse_logsheet_custom_csv(lines: List[str]) -> List[QsoRecord]:
    out: List[QsoRecord] = []
    data_lines = [ln for ln in lines if ln.strip()]
    if not data_lines:
        return out

    try:
        sample = data_lines[0]
        has_header = ("Date" in sample or "DATE" in sample) and ("Callsign" in sample or "CALLSIGN" in sample)

        if has_header:
            reader = csv.DictReader(data_lines)
            for row in reader:
                if not row:
                    continue
                date = (row.get("Date") or row.get("DATE") or "").strip()
                time = (row.get("Time") or row.get("TIME") or "").strip()
                call = (row.get("Callsign") or row.get("CALLSIGN") or "").strip()
                sent = (row.get("Sent") or row.get("SENT") or "").strip()
                rcvd = (row.get("Rcvd") or row.get("RCVD") or "").strip()
                mhz = (row.get("MHz") or row.get("MHZ") or row.get("Band") or row.get("BAND") or "").strip()
                mode = (row.get("Mode") or row.get("MODE") or "").strip()
                pts_s = (row.get("Pts") or row.get("PTS") or "").strip()

                if not _looks_date(date):
                    continue
                date = date.replace("/", "-")
                time = _parse_time(time)
                band = _parse_band_mhz(mhz)
                mode = mode or "AM"
                call = _clean_callsign(call)

                sent_exch = _canon_exchange(_extract_exchange_from_token(sent))
                rcvd_exch = _canon_exchange(_extract_exchange_from_token(rcvd))
                pt = _safe_int(pts_s, 0)
                if pt <= 0:
                    pt = 0 if pt == 0 and (str(row.get("Rmks", "")).lower().find("dupe") >= 0) else (2 if pt == 0 else pt)

                out.append(QsoRecord(
                    date=date, time=time, band_mhz=band, mode=mode,
                    worked_call=call, sent_exch=sent_exch, rcvd_exch=rcvd_exch,
                    pts=pt, dup=False, raw=",".join([v for v in row.values() if v is not None])
                ))
            return out

        for raw in data_lines:
            if "," not in raw:
                continue
            cols = [c.strip() for c in raw.split(",")]
            if len(cols) < 8:
                continue
            if not _looks_date(cols[0]):
                continue
            date = cols[0].replace("/", "-")
            time = _parse_time(cols[1])
            call = _clean_callsign(cols[2])
            sent = cols[3] if len(cols) > 3 else ""
            rcvd = cols[4] if len(cols) > 4 else ""
            band = _parse_band_mhz(cols[5] if len(cols) > 5 else "")
            mode = (cols[6] if len(cols) > 6 else "AM") or "AM"
            pt = _safe_int(cols[8] if len(cols) > 8 else (cols[-1] if cols else "2"), 0)
            if pt <= 0:
                if re.search(r",0\s*$", raw) or "dupe" in raw.lower():
                    pt = 0
                else:
                    pt = 2

            out.append(QsoRecord(
                date=date, time=time, band_mhz=band, mode=mode,
                worked_call=call,
                sent_exch=_canon_exchange(_extract_exchange_from_token(sent)),
                rcvd_exch=_canon_exchange(_extract_exchange_from_token(rcvd)),
                pts=pt, dup=False, raw=raw
            ))
        return out

    except Exception:
        for raw in data_lines:
            s = raw.strip()
            if not s or "," not in s:
                continue
            cols = [c.strip() for c in s.split(",")]
            if len(cols) < 6:
                continue
            if not _looks_date(cols[0]):
                continue
            date = cols[0].replace("/", "-")
            time = _parse_time(cols[1])
            call = _clean_callsign(cols[2]) if len(cols) > 2 else ""
            band = _parse_band_mhz(cols[5]) if len(cols) > 5 else ""
            mode = cols[6] if len(cols) > 6 else "AM"
            pt = _safe_int(cols[8] if len(cols) > 8 else (cols[-1] if cols else "2"), 2)
            out.append(QsoRecord(
                date=date, time=time, band_mhz=band, mode=mode,
                worked_call=call,
                sent_exch="",
                rcvd_exch="",
                pts=pt, dup=False, raw=raw
            ))
        return out

def parse_logsheet_generic(lines: List[str], logsheet_type: str) -> List[QsoRecord]:
    t = (logsheet_type or "").strip().upper()
    if "HLTST" in t:
        return parse_logsheet_hltst(lines)
    if "ZLOG" in t:
        return parse_logsheet_zlog(lines)
    if "自作" in t or "CSV" in t:
        return parse_logsheet_custom_csv(lines)
    if "CTESTWIN" in t or "LOGSHEETFORM" in t or t == "":
        return parse_logsheet_ctestwin(lines)
    qs = parse_logsheet_ctestwin(lines)
    if qs:
        return qs
    return parse_logsheet_custom_csv(lines)


# -----------------------------
# Submission parser (SUMMARYSHEET + LOGSHEET)
# -----------------------------

def split_submission_blocks(text: str) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    t = _clean(text)

    sm = re.search(r"(<SUMMARYSHEET\b.*?</SUMMARYSHEET>)", t, flags=re.DOTALL | re.IGNORECASE)
    summary_block = sm.group(1) if sm else None

    lm = re.search(r"(<LOGSHEET\b.*?</LOGSHEET>)", t, flags=re.DOTALL | re.IGNORECASE)
    log_block = lm.group(1) if lm else None

    log_type = None
    if log_block:
        log_type = _find_attr(log_block, "LOGSHEET", "TYPE")

    return summary_block, log_block, log_type

def parse_summarysheet(summary_block: str) -> Dict[str, Any]:
    sb = _clean(summary_block or "")
    d: Dict[str, Any] = {}
    d["contestname"] = _find_tag(sb, "CONTESTNAME") or ""
    d["categorycode"] = _find_tag(sb, "CATEGORYCODE") or ""
    d["categoryname"] = _find_tag(sb, "CATEGORYNAME") or ""
    d["callsign"] = _clean_callsign(_find_tag(sb, "CALLSIGN") or "")
    d["opcallsign"] = _clean_callsign(_find_tag(sb, "OPCALLSIGN") or "")

    d["address"] = _strip_tags_text(_find_tag(sb, "ADDRESS") or "")
    d["opplace"] = _strip_tags_text(_find_tag(sb, "OPPLACE") or "")

    d["comments"] = _strip_tags_text(_find_tag(sb, "COMMENTS") or "")

    score_50 = None
    m = re.search(r"<SCORE\b[^>]*BAND\s*=\s*(\"|')?50MHz\1?[^>]*>(.*?)</SCORE>", sb, flags=re.DOTALL | re.IGNORECASE)
    if m:
        score_50 = _strip_tags_text(m.group(2))
    if not score_50:
        m = re.search(r"<SCORE\b[^>]*BAND\s*=\s*(\"|')?TOTAL\1?[^>]*>(.*?)</SCORE>", sb, flags=re.DOTALL | re.IGNORECASE)
        if m:
            score_50 = _strip_tags_text(m.group(2))
    qso, pts, mult = _parse_score_triplet(score_50 or "")
    d["claimed_qso"] = qso
    d["claimed_pts"] = pts
    d["claimed_mult"] = mult
    d["claimed_total"] = _safe_int(_find_tag(sb, "TOTALSCORE"), 0)
    return d

def parse_logsheet_block(log_block: str, log_type: str) -> List[QsoRecord]:
    lb = _clean(log_block or "")
    inner = re.sub(r"^<LOGSHEET\b[^>]*>", "", lb, flags=re.IGNORECASE).strip()
    inner = re.sub(r"</LOGSHEET>\s*$", "", inner, flags=re.IGNORECASE).strip()
    lines = [ln.rstrip("\n") for ln in inner.split("\n")]
    return parse_logsheet_generic(lines, log_type or "")

def build_station_entry_from_text(
    text: str,
    fallback_callsign: str = "",
    fallback_opplace: str = "",
    source_name: str = ""
) -> StationEntry:
    summary_block, log_block, log_type = split_submission_blocks(text)

    entry = StationEntry()
    entry.source_name = source_name or ""
    entry.raw_submission_text = text or ""

    if summary_block:
        sd = parse_summarysheet(summary_block)
        entry.callsign = sd.get("callsign", "") or fallback_callsign
        entry.category = sd.get("categorycode", "") or ""
        entry.category_name = sd.get("categoryname", "") or ""
        entry.address = sd.get("address", "") or ""
        entry.comments = sd.get("comments", "") or ""

        opplace_raw = sd.get("opplace", "") or ""

        if _opplace_means_home(opplace_raw):
            base = entry.address
        else:
            base = opplace_raw

        opplace = normalize_opplace_any(base, entry.address)

        if fallback_opplace.strip():
            opplace = normalize_opplace_any(fallback_opplace.strip(), entry.address)

        entry.opplace = opplace

        entry.claimed_qso = sd.get("claimed_qso")
        entry.claimed_pts = sd.get("claimed_pts")
        entry.claimed_mult = sd.get("claimed_mult")
        entry.claimed_total = sd.get("claimed_total")
    else:
        entry.callsign = _clean_callsign(fallback_callsign)
        entry.opplace = normalize_opplace_any(fallback_opplace.strip(), "")

    if not entry.callsign:
        raise ValueError("CALLSIGN が見つかりません（SUMMARYSHEET が無い／CALLSIGN 空）")

    entry.logsheet_type = (log_type or "").strip()

    if log_block:
        entry.qsos = parse_logsheet_block(log_block, log_type or "")
    else:
        entry.qsos = []

    recalc_entry(entry)

    # ★チェックログ判定
    entry.is_checklog = (entry.callsign in CHECKLOG_CALLSIGNS)

    return entry


# -----------------------------
# Scoring / validation
# -----------------------------

def mark_duplicates(qsos: List[QsoRecord]) -> None:
    seen: set[Tuple[str, str, str]] = set()
    for q in qsos:
        key = (q.band_mhz.strip(), q.mode.strip().upper(), q.worked_call.strip().upper())
        if key in seen:
            q.dup = True
            q.pts = 0
        else:
            if q.pts == 0:
                q.dup = True
            else:
                q.dup = False
            seen.add(key)

def _apply_manual_override(entry: StationEntry) -> None:
    if not entry.manual_enabled:
        return

    if entry.manual_qso is not None:
        entry.recalced_qso = int(entry.manual_qso)
    if entry.manual_pts is not None:
        entry.recalced_pts = int(entry.manual_pts)
    if entry.manual_mult is not None:
        entry.recalced_mult = int(entry.manual_mult)
    if entry.manual_total is not None:
        entry.recalced_total = int(entry.manual_total)
    else:
        entry.recalced_total = int(entry.recalced_pts) * int(entry.recalced_mult)

    if entry.manual_opplace.strip():
        entry.opplace = normalize_opplace_any(entry.manual_opplace.strip(), entry.address)

def recalc_entry(entry: StationEntry) -> None:
    qsos = list(entry.qsos or [])
    mark_duplicates(qsos)

    valid = [q for q in qsos if (not q.dup) and q.pts > 0]
    entry.recalced_qso = len(valid)
    entry.recalced_pts = sum(int(q.pts) for q in valid)

    mult_set = set()
    for q in valid:
        ex = _canon_exchange(q.rcvd_exch)
        if ex:
            mult_set.add(ex)
    entry.recalced_mult = len(mult_set)
    entry.recalced_total = entry.recalced_pts * entry.recalced_mult

    _apply_manual_override(entry)

    if entry.claimed_total is not None and _safe_int(entry.claimed_total, 0) == 0:
        entry.match = True
        entry.reason = "申告が0のため 0扱い（訂正しない）"
        return

    reasons = []

    def add_reason(label: str, a: Optional[int], b: int) -> None:
        if a is None:
            return
        if _safe_int(a, -999999) != b:
            reasons.append(f"{label}差（申告{a}/再計算{b}）")

    add_reason("QSO数", entry.claimed_qso, entry.recalced_qso)
    add_reason("素点", entry.claimed_pts, entry.recalced_pts)
    add_reason("マルチ", entry.claimed_mult, entry.recalced_mult)
    add_reason("総得点", entry.claimed_total, entry.recalced_total)

    entry.match = (len(reasons) == 0)
    note = f" / 手動:{entry.manual_note}" if entry.manual_enabled and entry.manual_note.strip() else ""
    entry.reason = " / ".join(reasons) + note


# -----------------------------
# Ranking / Awards helpers
# -----------------------------

def _entry_rank_metrics(e: StationEntry) -> Tuple[int, int, int, int]:
    return (int(e.recalced_total), int(e.recalced_pts), int(e.recalced_mult), int(e.recalced_qso))

def rank_entries(entries: List[StationEntry]) -> List[Tuple[int, StationEntry]]:
    sorted_es = sorted(
        entries,
        key=lambda e: (-int(e.recalced_total), -int(e.recalced_pts), -int(e.recalced_mult), -int(e.recalced_qso), e.callsign)
    )
    ranked: List[Tuple[int, StationEntry]] = []
    prev_metrics: Optional[Tuple[int, int, int, int]] = None
    prev_rank = 0
    for i, e in enumerate(sorted_es, start=1):
        metrics = _entry_rank_metrics(e)
        if prev_metrics is not None and metrics == prev_metrics:
            rank = prev_rank
        else:
            rank = i
        ranked.append((rank, e))
        prev_metrics = metrics
        prev_rank = rank

    # `CHECKLOG`を独立した部門（CHECKLOG(主催者)）として追加
    checklog_entries = [e for e in entries if e.is_checklog]
    for e in checklog_entries:
        ranked.append((0, e))  # `CHECKLOG`を特別にリストに追加

    return ranked


def refresh_table(self) -> None:
    self.tree.delete(*self.tree.get_children())
    entries_sorted = sorted(self.entries.values(), key=lambda e: e.callsign)

    for e in entries_sorted:
        match_txt = "OK" if e.match else "差あり"
        cat_disp = category_display(e.category or "")

        # チェックログの場合は「CHECKLOG(主催者)」を表示
        if e.is_checklog:
            tag = "checklog"
            match_txt = "CHECKLOG(主催者)"
            cat_disp = "CHECKLOG(主催者)"  # CHECKLOG 部門
        elif e.manual_enabled:
            tag = "manual"
        else:
            tag = "good" if e.match else "bad"

        # コメントも反映
        comment = e.comments or ""  # コメントが空の場合も対応

        self.tree.insert(
            "",
            "end",
            iid=e.callsign,
            values=(
                e.callsign,
                cat_disp,
                e.opplace or "",
                e.recalced_qso,
                e.recalced_pts,
                e.recalced_mult,
                e.recalced_total,
                _safe_int(e.claimed_total, 0) if e.claimed_total is not None else "",
                match_txt,
                comment,  # コメントを表示
            ),
            tags=(tag,)
        )



def top_n_with_ties(entries: List[StationEntry], n: int) -> List[Tuple[int, StationEntry]]:
    ranked = rank_entries(entries)
    if n <= 0 or not ranked:
        return []
    if len(ranked) <= n:
        return ranked
    cutoff_rank, cutoff_entry = ranked[n-1]
    cutoff_metrics = _entry_rank_metrics(cutoff_entry)
    out: List[Tuple[int, StationEntry]] = []
    for r, e in ranked:
        if len(out) < n:
            out.append((r, e))
            continue
        if _entry_rank_metrics(e) == cutoff_metrics:
            out.append((r, e))
        else:
            break
    return out

import re
from typing import Optional

def extract_call_area_digit_base(callsign: str) -> Optional[int]:
    base = (callsign or "").strip().upper().split("/")[0]
    print(f"Extracting area from callsign: {callsign}, base: {base}")
    
    # 'split' の結果が空でないか確認
    parts = callsign.split("/")
    if len(parts) > 1:
        area = parts[1]
        print(f"Extracted area from callsign with /: {area}")
        return int(area)
    
    # エリアが指定されていない場合
    print(f"No area found for callsign: {callsign}")
    return None




# -----------------------------
# Export helpers (CTESTWIN normalize)
# -----------------------------

def qso_to_ctestwin_line(q: QsoRecord) -> str:
    date = (q.date or "").replace("/", "-").strip()
    time = _parse_time(q.time or "").strip()
    band = _canon_band_token(q.band_mhz) or "50"
    mode = (q.mode or "AM").strip().upper()
    call = _clean_callsign(q.worked_call or "")

    sent = _canon_exchange(q.sent_exch) or "-"
    rcvd = _canon_exchange(q.rcvd_exch) or "-"

    pts = _safe_int(q.pts, 2)
    return f"{date} {time} {band} {mode} {call} 59 {sent} 59 {rcvd} {pts}"

def replace_logsheet_with_ctestwin(raw_text: str, entry: StationEntry) -> str:
    t = _clean(raw_text or "")

    lines = [qso_to_ctestwin_line(q) for q in (entry.qsos or [])]
    new_log = "<LOGSHEET TYPE=CTESTWIN>\n" + "\n".join(lines) + "\n</LOGSHEET>"

    if re.search(r"<LOGSHEET\b.*?</LOGSHEET>", t, flags=re.DOTALL | re.IGNORECASE):
        return re.sub(r"<LOGSHEET\b.*?</LOGSHEET>", new_log, t, flags=re.DOTALL | re.IGNORECASE)

    sm = re.search(r"(<SUMMARYSHEET\b.*?</SUMMARYSHEET>)", t, flags=re.DOTALL | re.IGNORECASE)
    if sm:
        idx = sm.end()
        return t[:idx] + "\n" + new_log + "\n" + t[idx:]

    return (t.rstrip() + "\n" + new_log + "\n")


# -----------------------------
# Publish HTML helpers
# -----------------------------

def _rank_sort_key(e: StationEntry) -> Tuple[int, int, int, int, str]:
    return (
        -int(e.recalced_total),
        -int(e.recalced_pts),
        -int(e.recalced_mult),
        -int(e.recalced_qso),
        (e.callsign or ""),
    )


def _competition_ranks(entries_sorted: List[StationEntry]) -> List[Tuple[int, StationEntry]]:
    out: List[Tuple[int, StationEntry]] = []
    prev_total: Optional[int] = None
    rank = 0
    pos = 0
    for e in entries_sorted:
        pos += 1
        t = int(e.recalced_total)
        if prev_total is None or t != prev_total:
            rank = pos
            prev_total = t
        out.append((rank, e))
    return out

def _h(x: Any) -> str:
    return html.escape(str(x) if x is not None else "")

def _html_table(headers: List[str], rows: List[List[Any]]) -> str:
    th = "".join([f"<th>{_h(hd)}</th>" for hd in headers])
    trs = []
    for r in rows:
        tds = "".join([f"<td>{_h(v)}</td>" for v in r])
        trs.append(f"<tr>{tds}</tr>")
    return (
        "<table class='tbl'>"
        f"<thead><tr>{th}</tr></thead>"
        f"<tbody>{''.join(trs)}</tbody>"
        "</table>"
    )

def _html_page(title: str, body_html: str) -> str:
    css = """
    body{font-family:system-ui,-apple-system,Segoe UI,Roboto,Helvetica,Arial,'Noto Sans JP','Hiragino Kaku Gothic ProN',Meiryo,sans-serif; margin:24px; line-height:1.5;}
    h1{font-size:22px; margin:0 0 12px 0;}
    h2{font-size:18px; margin:26px 0 10px 0;}
    h3{font-size:16px; margin:18px 0 8px 0;}
    .meta{color:#555; font-size:12px; margin:0 0 14px 0;}
    .tbl{border-collapse:collapse; width:100%; font-size:13px;}
    .tbl th,.tbl td{border:1px solid #bbb; padding:7px 9px; vertical-align:top;}
    .tbl th{background:#f3f3f3; text-align:left;}
    .num{text-align:right;}
    .small{font-size:12px; color:#444;}
    a{color:#0b66c3; text-decoration:none;}
    a:hover{text-decoration:underline;}
    .toc a{display:inline-block; margin-right:12px; margin-bottom:6px;}
    .badge{display:inline-block; padding:2px 8px; border:1px solid #bbb; border-radius:999px; font-size:12px; margin-left:8px; color:#444;}
    .checklog{background:#fff3cd; border-color:#ffe69c;}
    """
    return (
        "<!doctype html>"
        "<html lang='ja'><head>"
        "<meta charset='utf-8'>"
        f"<title>{_h(title)}</title>"
        f"<style>{css}</style>"
        "</head><body>"
        f"<h1>{_h(title)}</h1>"
        f"{body_html}"
        "</body></html>"
    )

def category_display(code: str) -> str:
    c = (code or "").strip()
    if not c:
        return ""
    name = CATEGORY_LABELS.get(c, "")
    if name:
        return f"{c} {name}" if c != "SWL" else f"{name}"  # SWL 部門は "SWL" とだけ表示
    return c



# -----------------------------
# ★PDF Certificate / Entry Certificate
# -----------------------------

def _ensure_fonts() -> None:
    """
    ReportLab日本語フォントをCIDで登録（環境依存が少ない）
    """
    try:
        pdfmetrics.getFont("HeiseiKakuGo-W5")
    except:
        try:
            pdfmetrics.registerFont(UnicodeCIDFont("HeiseiKakuGo-W5"))
        except:
            # 最悪の場合：和文はHelveticaで出るが文字化けする可能性あり
            pass

def _wrap_by_width(text: str, font_name: str, font_size: int, max_width: float) -> List[str]:
    """
    文字幅（stringWidth）で簡易折り返し。日本語も1文字ずつ積み上げでOK。
    """
    if not text:
        return []
    out: List[str] = []
    cur = ""
    for ch in text:
        if ch == "\n":
            if cur:
                out.append(cur)
                cur = ""
            continue
        nxt = cur + ch
        try:
            w = pdfmetrics.stringWidth(nxt, font_name, font_size)
        except:
            w = len(nxt) * (font_size * 0.55)
        if w <= max_width:
            cur = nxt
        else:
            if cur:
                out.append(cur)
                cur = ch
            else:
                out.append(nxt)
                cur = ""
    if cur:
        out.append(cur)
    return out
def _text_width(text: str, font_name: str, font_size: int) -> float:
    try:
        return pdfmetrics.stringWidth(text, font_name, font_size)
    except Exception:
        # フォント未登録などの保険：ざっくり推定
        return len(text) * (font_size * 0.55)


def _split_two_lines_balanced(
    text: str,
    font_name: str,
    font_size: int,
    max_width: float,
) -> List[str]:
    """
    文章を「必ず2行」に分割し、2行の横幅がなるべく同じになる分割点を探す。
    - 両行とも max_width を超えない候補のみ採用
    - なるべく文として自然な区切り（「を」「に」「、」等）を優先
    - ASCII 連続列（例: "AM/50MHz" 等）が分断されないよう配慮
    """
    s = (text or "").strip()
    if not s:
        return ["", ""]

    # もし1行に収まればそのまま返す（2行固定が不要な場合）
    if _text_width(s, font_name, font_size) <= max_width:
        return [s]

    # 優先度の低い／高い切り分けポイントのペナルティ関数
    def boundary_penalty(left_last: str, right_first: str) -> float:
        # 強く推奨される切れ目（句読点、スペース）
        if left_last in ("、", "。", "　", " "):
            return 0.0
        # 助詞などは許容（小ペナルティ）
        if left_last in ("を", "に", "で", "と", "は", "が", "も", "へ", "や", "の"):
            return 0.2
        # 漢字->ひらがな の切り（動詞活用など）
        if (left_last >= "\u4e00" and left_last <= "\u9fff") and (right_first >= "\u3040" and right_first <= "\u309f"):
            return 0.5
        return 1.0

    def ascii_break_penalty(left_last: str, right_first: str) -> float:
        import string
        ascii_set = set(string.ascii_letters + string.digits + "/")
        if left_last in ascii_set and right_first in ascii_set:
            return 2.0
        return 0.0

    best = None  # (score, i, w1, w2)
    n = len(s)
    # 全分割点をスキャン（先頭や末尾は除外）
    for i in range(1, n):
        left = s[:i].rstrip()
        right = s[i:].lstrip()
        if not left or not right:
            continue

        left_last = left[-1]
        right_first = right[0]

        # 幅を計測
        w1 = _text_width(left, font_name, font_size)
        w2 = _text_width(right, font_name, font_size)

        # 両方が max_width を超える分割は無視
        if w1 > max_width or w2 > max_width:
            continue

        diff = abs(w1 - w2)
        score = diff
        score += boundary_penalty(left_last, right_first) * (font_size * 1.5)
        score += ascii_break_penalty(left_last, right_first) * (font_size * 3.0)

        if best is None or score < best[0]:
            best = (score, i, w1, w2)

    if best is None:
        # 良い2行分割が見つからない場合は幅に基づく通常折り返しにフォールバック
        return _wrap_by_width(s, font_name, font_size, max_width)[:2]

    i = best[1]
    return [s[:i].rstrip(), s[i:].lstrip()]

def _draw_center(c: rl_canvas.Canvas, text: str, y: float, font: str, size: int) -> None:
    c.setFont(font, size)
    w, _h = A4
    c.drawCentredString(w/2, y, text)

def _draw_multiline_center(c: rl_canvas.Canvas, lines: List[str], y_top: float, leading: float, font: str, size: int) -> float:
    """
    y_top から下に向けて複数行センター描画。描画後の最終yを返す。
    """
    c.setFont(font, size)
    w, _h = A4
    y = y_top
    for ln in lines:
        c.drawCentredString(w/2, y, ln)
        y -= leading
    return y

def _bg_path_from_folder(folder: str, filename: str) -> str:
    return os.path.join(folder, filename)

def generate_award_pdf_one(
    out_path: str,
    bg_path: str,
    callsign: str,
    year: int,
    category_code: str,
    rank: int,
    total_score: int,
) -> None:
    """
    賞状 1枚をPDF生成（A4縦）
    - 本文は「必ず2行」「幅がなるべく同じ」になるように分割
    - 年/部門順位/本文/日付/主催者名のサイズと位置を調整
    """
    _ensure_fonts()

    page_w, page_h = A4
    c = rl_canvas.Canvas(out_path, pagesize=A4)

    # 背景
    if bg_path and os.path.isfile(bg_path):
        img = ImageReader(bg_path)
        c.drawImage(img, 0, 0, width=page_w, height=page_h, preserveAspectRatio=False, mask='auto')

    # ----------------
    # レイアウト（調整しやすいように数値をまとめる）
    # ----------------
    y_title = page_h - 86*mm

    # ★年：下げて大きく
    y_year  = page_h - 106*mm
    year_size = 34

    # ★部門/順位：少し下げて大きく
    y_line1 = page_h - 122*mm
    line1_size = 16

    # コール
    y_call  = page_h - 146*mm
    call_size = 42

    # Total score
    y_score = page_h - 156*mm
    score_size = 16

    # ★本文：大きく、2行バランス
    y_body  = page_h - 176*mm
    body_size = 16
    body_leading = 9*mm

    # ★発行日：大きく
    y_date  = 84*mm
    date_size = 15

    # ★主催者名：少し上げて大きく
    y_org   = 66*mm
    org_size = 15
    # 年
    _draw_center(c, str(year), y_year, "Helvetica-Bold", year_size)
    # タイトル（和文）
    _draw_center(c, CONTEST_TITLE, y_title, "HeiseiKakuGo-W5", 18)


    # 部門 + 順位
    cat_disp = category_display(category_code)
    line1 = f"{cat_disp}  第{rank}位"
    _draw_center(c, line1, y_line1, "HeiseiKakuGo-W5", line1_size)

    # コール
    _draw_center(c, callsign, y_call, "Helvetica-Bold", call_size)

    # Total score
    _draw_center(c, f"Total Score  {total_score:,}", y_score, "Helvetica-Bold", score_size)

    # 本文（必ず2行・幅を揃える）
    max_text_w = page_w - 60*mm
    body = AWARD_SENTENCE.strip()

    # まず指定サイズで2行化、収まらない場合はサイズを落として再試行
    fs = body_size
    while fs >= 12:
        lines2 = _split_two_lines_balanced(body, "HeiseiKakuGo-W5", fs, max_text_w)
        if len(lines2) >= 2:
            w1 = _text_width(lines2[0], "HeiseiKakuGo-W5", fs)
            w2 = _text_width(lines2[1], "HeiseiKakuGo-W5", fs)
            if w1 <= max_text_w and w2 <= max_text_w:
                break
        fs -= 1
    else:
        lines2 = _wrap_by_width(body, "HeiseiKakuGo-W5", 12, max_text_w)[:2]
        fs = 12

    _draw_multiline_center(c, lines2[:2], y_body, leading=body_leading, font="HeiseiKakuGo-W5", size=fs)

    # 発行日
    today = datetime.now().strftime("%Y年%m月%d日")
    _draw_center(c, today, y_date, "HeiseiKakuGo-W5", date_size)

    # 主催者名
    _draw_center(c, ORGANIZER_NAME, y_org, "HeiseiKakuGo-W5", org_size)

    c.showPage()
    c.save()



    """
    text を「2行」に分割し、2行の幅がなるべく同じになる分割点を探す。
    両行とも max_width を超えない範囲でベストを選ぶ。
    無理なら通常の _wrap_by_width にフォールバック。
    """
    s = (text or "").replace("\n", "").strip()
    if not s:
        return []

    # 1行に収まるならそのまま
    if _text_width(s, font_name, font_size) <= max_width:
        return [s]

    # 2行目先頭に来ると不自然な記号は避ける（必要なら増やしてOK）
    bad_line2_head = set("、。,.)]】』」〉》）:;!?％%ー—‐-")

    best = None
    n = len(s)
    mid = n / 2.0

    for i in range(1, n):
        l1 = s[:i].rstrip()
        l2 = s[i:].lstrip()
        if not l1 or not l2:
            continue
        if l2[0] in bad_line2_head:
            continue

        w1 = _text_width(l1, font_name, font_size)
        w2 = _text_width(l2, font_name, font_size)

        if w1 > max_width or w2 > max_width:
            continue

        # 幅の差を最小化。ついでに真ん中寄りを少し優先
        score = abs(w1 - w2) + abs(i - mid) * 0.05
        if (best is None) or (score < best[0]):
            best = (score, l1, l2)

    if best:
        return [best[1], best[2]]

    # どうしても2行に収まらない（or良い分割が無い）場合は通常折り返し
    return _wrap_by_width(s, font_name, font_size, max_width)


def generate_entry_pdf_one(
    out_path: str,
    bg_path: str,
    callsign: str,
    year: int,
    category_code: str,
    total_score: int,
) -> None:
    """
    参加証 1枚（A4縦）
    改善点：年・部門・本文・主催者を見やすく（大きく＆配置調整）
    """
    _ensure_fonts()

    page_w, page_h = A4
    c = rl_canvas.Canvas(out_path, pagesize=A4)

    if bg_path and os.path.isfile(bg_path):
        img = ImageReader(bg_path)
        c.drawImage(img, 0, 0, width=page_w, height=page_h, preserveAspectRatio=False, mask="auto")

    # --- レイアウト（mm）---
    y_title = page_h - 106*mm
    y_year  = page_h - 92*mm
    y_line1 = page_h - 112*mm
    y_call  = page_h - 162*mm
    y_score = page_h - 172*mm
    y_body  = page_h - 192*mm
    y_org   = 72*mm

    # --- サイズ ---
    fs_title = 26
    fs_year  = 42
    fs_line1 = 18
    fs_call  = 42
    fs_score = 16
    fs_body  = 14
    fs_org   = 16

    _draw_center(c, f"{CONTEST_TITLE} 参加証", y_title, "HeiseiKakuGo-W5", fs_title)
    _draw_center(c, str(year), y_year, "Helvetica-Bold", fs_year)

    cat_disp = category_display(category_code)
    _draw_center(c, cat_disp, y_line1, "HeiseiKakuGo-W5", fs_line1)

    _draw_center(c, callsign, y_call, "Helvetica-Bold", fs_call)
    _draw_center(c, f"Total Score  {total_score:,}", y_score, "Helvetica-Bold", fs_score)

    body = f"{CONTEST_TITLE}にご参加いただき\nありがとうございました"
    lines = _wrap_by_width(body, "HeiseiKakuGo-W5", fs_body, page_w - 60*mm)
    _draw_multiline_center(c, lines, y_top=y_body, leading=7*mm, font="HeiseiKakuGo-W5", size=fs_body)


    _draw_center(c, ORGANIZER_NAME, y_org, "HeiseiKakuGo-W5", fs_org)

    c.showPage()
    c.save()


def _safe_filename(s: str) -> str:
    return re.sub(r'[\\/:*?"<>|]+', "_", (s or "").strip())

def build_award_lists(entries: List[StationEntry]) -> Tuple[List[Tuple[str, int, StationEntry]], List[Tuple[int, int, StationEntry]]]:
    valid_entries = [e for e in entries if not e.is_checklog]

    # 1F, 1P, 1Q, SWL 部門の局を抽出
    in_area_cats = {"1F", "1P", "1Q", "SWL"}
    in_entries = [e for e in valid_entries if (e.category or "").strip() in in_area_cats]

    # 1X 部門（1エリア外局）の局を抽出
    out_entries = [e for e in valid_entries if (e.category or "").strip() == "1X"]

    rows_in: List[Tuple[str, int, StationEntry]] = []
    cats = sorted({(e.category or "").strip() for e in in_entries})
    
    # 各部門で上位3位を抽出
    for cat in cats:
        es = [e for e in in_entries if (e.category or "").strip() == cat]
        winners = top_n_with_ties(es, 3)
        for rank, e in winners:
            rows_in.append((cat, rank, e))

    # 1X 部門でエリアごとに1位を抽出
    rows_out: List[Tuple[int, int, StationEntry]] = []
    area_winners = {}

    for e in out_entries:
        area = extract_call_area_digit_base(e.callsign)
        print(f"Checking {e.callsign} with area {area} and recalced_total {e.recalced_total}")  # デバッグ用出力

        if area is not None:
            # エリアごとの最高得点の局を選択
            if area not in area_winners or e.recalced_total > area_winners[area].recalced_total:
                area_winners[area] = e

    # 各エリア1位の局を表示
    for area, e in area_winners.items():
        print(f"Area {area} winner: {e.callsign}, score: {e.recalced_total}")  # デバッグ用出力
        rows_out.append((area, 1, e))

    return rows_in, rows_out


# -----------------------------
# GUI
# -----------------------------

class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("コンテスト集計チェッカー（単体 main.py）")
        self.geometry("1400x820")

        self.folder_var = tk.StringVar(value=os.path.abspath(os.getcwd()))
        self.callsign_var = tk.StringVar(value="")
        self.opplace_var = tk.StringVar(value="")

        self.entries: Dict[str, StationEntry] = {}
        self.override_path: Optional[str] = None

        self._build_ui()

    def _get_override_path(self) -> str:
        folder = self.folder_var.get().strip()
        return os.path.join(folder, "manual_overrides.json")

    def load_overrides(self) -> Dict[str, Any]:
        path = self._get_override_path()
        self.override_path = path
        if not os.path.isfile(path):
            return {}
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                return data
            return {}
        except Exception:
            return {}

    def save_overrides(self) -> None:
        if not self.override_path:
            self.override_path = self._get_override_path()
        data: Dict[str, Any] = {}
        for cs, e in self.entries.items():
            if e.manual_enabled:
                data[cs] = {
                    "enabled": True,
                    "qso": e.manual_qso,
                    "pts": e.manual_pts,
                    "mult": e.manual_mult,
                    "total": e.manual_total,
                    "note": e.manual_note,
                    "opplace": e.manual_opplace,
                }
        try:
            with open(self.override_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as ex:
            messagebox.showwarning("保存失敗", f"manual_overrides.json の保存に失敗しました。\n{ex}")

    def apply_overrides_to_entries(self) -> None:
        data = self.load_overrides()
        for cs, e in self.entries.items():
            od = data.get(cs)
            if not isinstance(od, dict):
                continue
            e.manual_enabled = bool(od.get("enabled", True))
            e.manual_qso = od.get("qso", None)
            e.manual_pts = od.get("pts", None)
            e.manual_mult = od.get("mult", None)
            e.manual_total = od.get("total", None)
            e.manual_note = str(od.get("note", "") or "")
            e.manual_opplace = str(od.get("opplace", "") or "")
            recalc_entry(e)

    def _build_ui(self) -> None:
        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=8)

        ttk.Label(top, text="フォルダ:").pack(side="left")
        self.folder_entry = ttk.Entry(top, textvariable=self.folder_var, width=65)
        self.folder_entry.pack(side="left", padx=(6, 6))
        ttk.Button(top, text="フォルダ選択", command=self.on_select_folder).pack(side="left", padx=3)
        ttk.Button(top, text="再読み込み/再計算", command=self.on_reload).pack(side="left", padx=3)
        ttk.Button(top, text="CSV出力", command=self.on_export_csv).pack(side="left", padx=3)
        ttk.Button(top, text="LOG保存(CTESTWIN化)", command=self.on_export_logs_ctestwin).pack(side="left", padx=3)
        ttk.Button(top, text="発表用CSV出力(部門別+総合)", command=self.on_export_results).pack(side="left", padx=3)
        ttk.Button(top, text="コメント一覧CSV", command=self.on_export_comments_list).pack(side="left", padx=3)
        ttk.Button(top, text="入賞抽出CSV", command=self.on_export_awards).pack(side="left", padx=3)
        ttk.Button(top, text="発表HTML出力(部門別+総合)", command=self.on_export_html).pack(side="left", padx=3)

        # ★追加：証書PDF
        ttk.Button(top, text="賞状PDF出力（入賞）", command=self.on_export_award_pdfs).pack(side="left", padx=(18, 3))
        ttk.Button(top, text="参加証PDF出力（参加者全員）", command=self.on_export_entry_pdfs).pack(side="left", padx=3)

        ttk.Button(top, text="手動訂正", command=self.on_manual_edit_selected).pack(side="left", padx=(18, 3))
        ttk.Button(top, text="訂正クリア", command=self.on_manual_clear_selected).pack(side="left", padx=3)

        paste_frame = ttk.LabelFrame(self, text="LOGSHEET貼り付け（任意：ファイルが無い局をここから追加）")
        paste_frame.pack(fill="x", padx=10, pady=(0, 8))

        row1 = ttk.Frame(paste_frame)
        row1.pack(fill="x", padx=8, pady=6)

        ttk.Label(row1, text="局コールサイン（任意：SUMMARYから自動取得可）:").pack(side="left")
        ttk.Entry(row1, textvariable=self.callsign_var, width=18).pack(side="left", padx=(6, 14))
        ttk.Label(row1, text="運用地（任意）:").pack(side="left")
        ttk.Entry(row1, textvariable=self.opplace_var, width=60).pack(side="left", padx=(6, 10))

        ttk.Button(row1, text="貼り付け内容を追加", command=self.on_add_paste).pack(side="left", padx=4)
        ttk.Button(row1, text="入力欄クリア", command=self.on_clear_paste).pack(side="left", padx=4)

        self.paste_text = tk.Text(paste_frame, height=7, wrap="none")
        self.paste_text.pack(fill="x", padx=8, pady=(0, 8))
        self._make_text_context_menu(self.paste_text)

        table_frame = ttk.Frame(self)
        table_frame.pack(fill="both", expand=True, padx=10, pady=8)

        columns = (
            "callsign", "category", "opplace",
            "qso", "pts", "mult", "re_total",
            "cl_total", "match", "reason"
        )
        self.tree = ttk.Treeview(table_frame, columns=columns, show="headings", height=18)
        self.tree.heading("callsign", text="コールサイン")
        self.tree.heading("category", text="部門")
        self.tree.heading("opplace", text="運用地")
        self.tree.heading("qso", text="有効QSO数")
        self.tree.heading("pts", text="素点")
        self.tree.heading("mult", text="マルチ")
        self.tree.heading("re_total", text="再計算 総得点")
        self.tree.heading("cl_total", text="申告 総得点")
        self.tree.heading("match", text="一致？")
        self.tree.heading("reason", text="差あり原因（推定）")

        self.tree.column("callsign", width=90, anchor="w")
        self.tree.column("category", width=130, anchor="w")
        self.tree.column("opplace", width=420, anchor="w")
        self.tree.column("qso", width=90, anchor="e")
        self.tree.column("pts", width=70, anchor="e")
        self.tree.column("mult", width=70, anchor="e")
        self.tree.column("re_total", width=110, anchor="e")
        self.tree.column("cl_total", width=110, anchor="e")
        self.tree.column("match", width=70, anchor="center")
        self.tree.column("reason", width=380, anchor="w")

        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(table_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")

        table_frame.rowconfigure(0, weight=1)
        table_frame.columnconfigure(0, weight=1)

        self.tree.tag_configure("bad", foreground="red")
        self.tree.tag_configure("good", foreground="black")
        self.tree.tag_configure("manual", foreground="blue")
        self.tree.tag_configure("checklog", foreground="#b06a00")

        self.tree.bind("<Double-1>", self.on_open_detail)
        self._make_tree_context_menu()

        self.status_var = tk.StringVar(value="未読込")
        status = ttk.Label(self, textvariable=self.status_var, anchor="w")
        status.pack(fill="x", padx=10, pady=(0, 8))

        self.on_reload()

    def _make_text_context_menu(self, widget: tk.Text) -> None:
        menu = tk.Menu(widget, tearoff=0)
        menu.add_command(label="切り取り", command=lambda: widget.event_generate("<<Cut>>"))
        menu.add_command(label="コピー", command=lambda: widget.event_generate("<<Copy>>"))
        menu.add_command(label="貼り付け", command=lambda: widget.event_generate("<<Paste>>"))
        menu.add_separator()
        menu.add_command(label="すべて選択", command=lambda: self._select_all(widget))

        def popup(event):
            try:
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()

        widget.bind("<Button-3>", popup)

    def _make_tree_context_menu(self) -> None:
        menu = tk.Menu(self, tearoff=0)
        menu.add_command(label="手動訂正", command=self.on_manual_edit_selected)
        menu.add_command(label="訂正クリア", command=self.on_manual_clear_selected)

        def popup(event):
            iid = self.tree.identify_row(event.y)
            if iid:
                self.tree.selection_set(iid)
                self.tree.focus(iid)
            try:
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()

        self.tree.bind("<Button-3>", popup)

    def _select_all(self, widget: tk.Text) -> None:
        widget.tag_add("sel", "1.0", "end-1c")
        widget.mark_set("insert", "1.0")
        widget.see("insert")

    def on_select_folder(self) -> None:
        d = filedialog.askdirectory(initialdir=self.folder_var.get() or os.getcwd())
        if d:
            self.folder_var.set(d)

    def on_clear_paste(self) -> None:
        self.paste_text.delete("1.0", "end")
        self.callsign_var.set("")
        self.opplace_var.set("")

    def on_add_paste(self) -> None:
        text = self.paste_text.get("1.0", "end-1c").strip()
        if not text:
            messagebox.showwarning("不足", "貼り付け欄が空です。")
            return

        callsign = _clean_callsign(self.callsign_var.get())

        if not callsign:
            try:
                summary_block, _, _ = split_submission_blocks(text)
                if summary_block:
                    sd = parse_summarysheet(summary_block)
                    cs2 = _clean_callsign(sd.get("callsign", "") or "")
                    if cs2:
                        callsign = cs2
                        self.callsign_var.set(callsign)
            except Exception:
                pass

        if not callsign:
            messagebox.showwarning(
                "不足",
                "局コールサインが必要です。\n"
                "入力欄に入れるか、貼り付け内容に <SUMMARYSHEET> と <CALLSIGN> を含めてください。"
            )
            return

        opplace = self.opplace_var.get().strip()

        try:
            entry = build_station_entry_from_text(
                text=text,
                fallback_callsign=callsign,
                fallback_opplace=opplace,
                source_name="(貼り付け追加)"
            )
            self.entries[entry.callsign] = entry

            self.apply_overrides_to_entries()
            self.refresh_table()

            self.paste_text.delete("1.0", "end")
            self.callsign_var.set("")
            self.opplace_var.set("")

            self.status_var.set(f"貼り付け追加: {entry.callsign} を追加しました")
        except Exception as e:
            messagebox.showerror("解析エラー", f"貼り付け内容の解析に失敗しました。\n\n{e}")

    def on_reload(self) -> None:
        folder = self.folder_var.get().strip()
        if not folder or not os.path.isdir(folder):
            messagebox.showwarning("フォルダ", "有効なフォルダを選択してください。")
            return

        new_entries: Dict[str, StationEntry] = {}
        errors: List[str] = []

        patterns = ["*.log", "*.txt", "*.dat", "*.adi", "*.sum", "*.xml"]
        files = []
        for p in patterns:
            files.extend(glob.glob(os.path.join(folder, p)))
        files = sorted(set(files))

        for fp in files:
            try:
                with open(fp, "r", encoding="utf-8", errors="ignore") as f:
                    text = f.read()
                entry = build_station_entry_from_text(
                    text=text,
                    fallback_callsign="",
                    fallback_opplace="",
                    source_name=os.path.basename(fp)
                )
                if entry.callsign:
                    new_entries[entry.callsign] = entry
            except Exception as e:
                errors.append(f"{os.path.basename(fp)}: {e}")

        self.entries.update(new_entries)
        self.apply_overrides_to_entries()

        # ★チェックログ再判定
        for e in self.entries.values():
            e.is_checklog = (e.callsign in CHECKLOG_CALLSIGNS)

        self.refresh_table()

        ok = sum(1 for e in self.entries.values() if e.match)
        ng = sum(1 for e in self.entries.values() if not e.match)
        manual = sum(1 for e in self.entries.values() if e.manual_enabled)
        checklog = sum(1 for e in self.entries.values() if e.is_checklog)
        msg = f"完了: Summary={len(self.entries)}局 / OK={ok} / 差あり={ng} / 手動訂正={manual} / CHECKLOG={checklog}"
        if errors:
            msg += f" / 読込エラー={len(errors)}（詳細はコンソール）"
            print("---- load errors ----")
            for x in errors[:200]:
                print(x)
        self.status_var.set(msg)

    def refresh_table(self) -> None:
        self.tree.delete(*self.tree.get_children())
        entries_sorted = sorted(self.entries.values(), key=lambda e: e.callsign)

        for e in entries_sorted:
            match_txt = "OK" if e.match else "差あり"
            cat_disp = category_display(e.category or "")

            if e.is_checklog:
                tag = "checklog"
                match_txt = "CHECKLOG"
            elif e.manual_enabled:
                tag = "manual"
            else:
                tag = "good" if e.match else "bad"

            self.tree.insert(
                "",
                "end",
                iid=e.callsign,
                values=(
                    e.callsign,
                    cat_disp,
                    e.opplace or "",
                    e.recalced_qso,
                    e.recalced_pts,
                    e.recalced_mult,
                    e.recalced_total,
                    _safe_int(e.claimed_total, 0) if e.claimed_total is not None else "",
                    match_txt,
                    e.reason or "",
                ),
                tags=(tag,)
            )

    def _get_selected_callsign(self) -> Optional[str]:
        item = self.tree.focus()
        if not item:
            sel = self.tree.selection()
            if sel:
                item = sel[0]
        return item or None

    def on_manual_edit_selected(self) -> None:
        cs = self._get_selected_callsign()
        if not cs:
            messagebox.showinfo("手動訂正", "一覧から局を選択してください。")
            return
        e = self.entries.get(cs)
        if not e:
            return
        ManualEditDialog(self, e, on_saved=self._on_manual_saved)

    def _on_manual_saved(self) -> None:
        for e in self.entries.values():
            recalc_entry(e)
        self.save_overrides()
        self.refresh_table()
        self.status_var.set("手動訂正を保存しました（manual_overrides.json）")

    def on_manual_clear_selected(self) -> None:
        cs = self._get_selected_callsign()
        if not cs:
            messagebox.showinfo("訂正クリア", "一覧から局を選択してください。")
            return
        e = self.entries.get(cs)
        if not e:
            return
        if not e.manual_enabled:
            messagebox.showinfo("訂正クリア", f"{cs} は手動訂正がありません。")
            return
        if not messagebox.askyesno("訂正クリア", f"{cs} の手動訂正を削除しますか？"):
            return
        e.manual_enabled = False
        e.manual_qso = None
        e.manual_pts = None
        e.manual_mult = None
        e.manual_total = None
        e.manual_note = ""
        e.manual_opplace = ""
        recalc_entry(e)
        self.save_overrides()
        self.refresh_table()
        self.status_var.set(f"{cs} の手動訂正を削除しました")

    def on_open_detail(self, event=None) -> None:
        item = self.tree.focus()
        if not item:
            return
        callsign = item
        e = self.entries.get(callsign)
        if not e:
            return
        DetailWindow(self, e)

    # --- 既存のCSV/HTML出力（省略せず残す） ---
    # ※ここは元のまま（あなたの得点ロジックは触っていません）
    # ただし、PDF追加のためにこの下にPDF出力関数だけ追加します

    def on_export_logs_ctestwin(self) -> None:
        if not self.entries:
            messagebox.showinfo("LOG保存", "出力するデータがありません。")
            return

        out_dir = filedialog.askdirectory(
            initialdir=self.folder_var.get() or os.getcwd(),
            title="保存先フォルダを選択（局ごとに *.log を出力：LOGSHEETはCTESTWIN化）"
        )
        if not out_dir:
            return

        saved = 0
        skipped = 0
        errors: List[str] = []

        for e in sorted(self.entries.values(), key=lambda x: x.callsign):
            try:
                base_text = e.raw_submission_text or ""

                if base_text.strip():
                    out_text = replace_logsheet_with_ctestwin(base_text, e)
                else:
                    lines = "\n".join([qso_to_ctestwin_line(q) for q in (e.qsos or [])])
                    out_text = (
                        "<SUMMARYSHEET VERSION=R1.0>\n"
                        f"<CALLSIGN>{e.callsign}</CALLSIGN>\n"
                        f"<CATEGORYCODE>{e.category}</CATEGORYCODE>\n"
                        f"<CATEGORYNAME>{e.category_name}</CATEGORYNAME>\n"
                        f"<OPPLACE>{e.opplace}</OPPLACE>\n"
                        f"<TOTALSCORE>{_safe_int(e.claimed_total, 0) if e.claimed_total is not None else 0}</TOTALSCORE>\n"
                        "</SUMMARYSHEET>\n"
                        "<LOGSHEET TYPE=CTESTWIN>\n"
                        f"{lines}\n"
                        "</LOGSHEET>\n"
                    )

                safe_cs = re.sub(r'[\\/:*?"<>|]+', "_", e.callsign)
                out_name = f"{safe_cs}.log"
                out_path = os.path.join(out_dir, out_name)

                if os.path.exists(out_path):
                    if not messagebox.askyesno("上書き確認", f"既に存在します。\n上書きしますか？\n\n{out_path}"):
                        skipped += 1
                        continue

                with open(out_path, "w", encoding="utf-8", newline="\n") as f:
                    f.write(out_text)

                saved += 1

            except Exception as ex:
                errors.append(f"{e.callsign}: {ex}")

        msg = f"LOG保存(CTESTWIN化) 完了: 保存={saved} / スキップ={skipped}"
        if errors:
            msg += f" / エラー={len(errors)}（詳細はコンソール）"
            print("---- export log errors ----")
            for x in errors[:200]:
                print(x)

        self.status_var.set(msg)
        messagebox.showinfo("LOG保存", msg)

    def on_export_csv(self) -> None:
        if not self.entries:
            messagebox.showinfo("CSV", "出力するデータがありません。")
            return
        folder = self.folder_var.get().strip()
        default_name = os.path.join(folder, "contest_check_result.csv")
        fp = filedialog.asksaveasfilename(
            initialdir=folder,
            initialfile=os.path.basename(default_name),
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv")]
        )
        if not fp:
            return

        cols = [
            "callsign", "category", "opplace",
            "recalced_qso", "recalced_pts", "recalced_mult", "recalced_total",
            "claimed_qso", "claimed_pts", "claimed_mult", "claimed_total",
            "manual_enabled", "manual_qso", "manual_pts", "manual_mult", "manual_total", "manual_note",
            "manual_opplace",
            "match", "reason", "source"
        ]
        try:
            with open(fp, "w", encoding="utf-8-sig", newline="") as f:
                w = csv.writer(f)
                w.writerow(cols)
                for e in sorted(self.entries.values(), key=lambda x: x.callsign):
                    w.writerow([
                        e.callsign,
                        e.category,
                        e.opplace,
                        e.recalced_qso, e.recalced_pts, e.recalced_mult, e.recalced_total,
                        e.claimed_qso if e.claimed_qso is not None else "",
                        e.claimed_pts if e.claimed_pts is not None else "",
                        e.claimed_mult if e.claimed_mult is not None else "",
                        e.claimed_total if e.claimed_total is not None else "",
                        "YES" if e.manual_enabled else "NO",
                        e.manual_qso if e.manual_qso is not None else "",
                        e.manual_pts if e.manual_pts is not None else "",
                        e.manual_mult if e.manual_mult is not None else "",
                        e.manual_total if e.manual_total is not None else "",
                        e.manual_note,
                        e.manual_opplace,
                        "OK" if e.match else "NG",
                        e.reason,
                        e.source_name
                    ])
            self.status_var.set(f"CSV出力: {fp}")
        except Exception as ex:
            messagebox.showerror("CSV出力エラー", str(ex))

    def _csv_safe(self, s: str) -> str:
        return re.sub(r"[\r\n\t]+", " ", (s or "")).strip()

    def on_export_results(self) -> None:
        if not self.entries:
            messagebox.showinfo("発表用CSV", "出力するデータがありません。")
            return
        out_dir = filedialog.askdirectory(
            initialdir=self.folder_var.get() or os.getcwd(),
            title="保存先フォルダを選択（総合＋部門別の発表用CSVを出力）"
        )
        if not out_dir:
            return

        def write_csv(path: str, ranked: List[Tuple[int, StationEntry]]) -> None:
            cols = ["rank","callsign","categorycode","categoryname","opplace","valid_qso","pts","mult","total","manual_note","comments"]
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                w = csv.writer(f)
                w.writerow(cols)
                for rank, e in ranked:
                    w.writerow([
                        rank,
                        e.callsign,
                        e.category or "",
                        category_display(e.category or ""),
                        e.opplace or "",
                        int(e.recalced_qso),
                        int(e.recalced_pts),
                        int(e.recalced_mult),
                        int(e.recalced_total),
                        self._csv_safe(e.manual_note) if e.manual_enabled else "",
                        self._csv_safe(e.comments),
                    ])

        overall_path = os.path.join(out_dir, "results_overall.csv")
        all_for_rank = [e for e in self.entries.values() if not e.is_checklog]
        write_csv(overall_path, rank_entries(all_for_rank))

        cats = sorted({(e.category or "").strip() for e in all_for_rank if (e.category or "").strip()})
        for cat in cats:
            es = [e for e in all_for_rank if (e.category or "").strip() == cat]
            if not es:
                continue
            out_name = f"results_by_category_{cat}.csv"
            write_csv(os.path.join(out_dir, out_name), rank_entries(es))

        self.status_var.set(f"発表用CSV出力: {out_dir}")
        messagebox.showinfo("発表用CSV", "出力しました。\n\n- results_overall.csv\n- results_by_category_<CATEGORYCODE>.csv")

    def on_export_comments_list(self) -> None:
        if not self.entries:
            messagebox.showinfo("コメント一覧CSV", "出力するデータがありません。")
            return
        out_dir = filedialog.askdirectory(
            initialdir=self.folder_var.get() or os.getcwd(),
            title="保存先フォルダを選択（コメント一覧CSVを出力）"
        )
        if not out_dir:
            return
        path = os.path.join(out_dir, "comments_list.csv")
        cols = ["callsign","categorycode","categoryname","opplace","comments"]
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                w = csv.writer(f)
                w.writerow(cols)
                for e in sorted(self.entries.values(), key=lambda x: x.callsign):
                    if e.is_checklog:
                        continue
                    w.writerow([
                        e.callsign,
                        e.category or "",
                        category_display(e.category or ""),
                        e.opplace or "",
                        self._csv_safe(e.comments),
                    ])
            self.status_var.set(f"コメント一覧CSV出力: {path}")
            messagebox.showinfo("コメント一覧CSV", "出力しました。\n\n- comments_list.csv")
        except Exception as ex:
            messagebox.showerror("コメント一覧CSV出力エラー", str(ex))

    def on_export_awards(self) -> None:
        if not self.entries:
            messagebox.showinfo("入賞抽出CSV", "出力するデータがありません。")
            return
        out_dir = filedialog.askdirectory(
            initialdir=self.folder_var.get() or os.getcwd(),
            title="保存先フォルダを選択（入賞抽出CSVを出力）"
        )
        if not out_dir:
            return

        all_entries = [e for e in self.entries.values() if not e.is_checklog]

        rows_in, rows_out = build_award_lists(all_entries)

        path_in1 = os.path.join(out_dir, "awards_in1_by_category.csv")
        cols_in1 = ["categorycode","rank","callsign","categoryname","opplace","valid_qso","pts","mult","total","manual_note","comments"]
        with open(path_in1, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f)
            w.writerow(cols_in1)
            for cat, rank, e in rows_in:
                w.writerow([
                    cat,
                    rank,
                    e.callsign,
                    category_display(e.category or ""),
                    e.opplace or "",
                    int(e.recalced_qso),
                    int(e.recalced_pts),
                    int(e.recalced_mult),
                    int(e.recalced_total),
                    self._csv_safe(e.manual_note) if e.manual_enabled else "",
                    self._csv_safe(e.comments),
                ])

        path_out = os.path.join(out_dir, "awards_1x_by_area.csv")
        cols_out = ["area","rank","callsign","categorycode","categoryname","opplace","valid_qso","pts","mult","total","manual_note","comments"]
        with open(path_out, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f)
            w.writerow(cols_out)
            for d, rank, e in rows_out:
                w.writerow([
                    d,
                    rank,
                    e.callsign,
                    e.category or "",
                    category_display(e.category or ""),
                    e.opplace or "",
                    int(e.recalced_qso),
                    int(e.recalced_pts),
                    int(e.recalced_mult),
                    int(e.recalced_total),
                    self._csv_safe(e.manual_note) if e.manual_enabled else "",
                    self._csv_safe(e.comments),
                ])

        self.status_var.set(f"入賞抽出CSV: {out_dir}")
        messagebox.showinfo("入賞抽出CSV", "出力しました。\n\n- awards_in1_by_category.csv\n- awards_1x_by_area.csv")

    def on_export_html(self) -> None:
        if not self.entries:
            messagebox.showinfo("発表HTML", "出力するデータがありません。")
            return
        out_dir = filedialog.askdirectory(
            initialdir=self.folder_var.get() or os.getcwd(),
            title="保存先フォルダを選択（発表用HTMLを出力）"
        )
        if not out_dir:
            return

        entries_all = [e for e in self.entries.values() if not e.is_checklog]
        overall_sorted = sorted(entries_all, key=_rank_sort_key)
        overall_ranked = _competition_ranks(overall_sorted)

        def row_basic(rank: int, e: StationEntry) -> List[Any]:
            return [
                rank,
                e.callsign,
                category_display(e.category or ""),
                e.opplace or "",
                e.recalced_qso,
                e.recalced_pts,
                e.recalced_mult,
                e.recalced_total,
            ]

        body = []
        body.append("<p class='meta'>※ 同点は同順位（総得点が同じ局は同順位）。HTMLはブラウザで開いて、そのまま印刷→PDF保存できます。</p>")

        body.append("<div class='toc'>"
                    "<a href='#awards_in'>入賞（1F/1P/1Q/SWL：部門別上位3位）</a>"
                    "<a href='#awards_1x'>入賞（1X：各エリア1位）</a>"
                    "<a href='#overall'>総合結果</a>"
                    "<a href='#bycat'>部門別結果</a>"
                    "<a href='#comments'>コメント一覧</a>"
                    "</div>")

        rows_in, rows_out = build_award_lists(entries_all)

        body.append("<h2 id='awards_in'>入賞（1F/1P/1Q/SWL：各部門 上位3位まで）</h2>")
        if not rows_in:
            body.append("<p class='small'>対象局なし</p>")
        else:
            headers = ["順位", "コール", "部門", "運用地", "有効QSO", "素点", "マルチ", "総得点"]
            for cat in sorted({cat for cat, _, _ in rows_in}):
                body.append(f"<h3>{_h(category_display(cat))}</h3>")
                winners = [(r, e) for (c, r, e) in rows_in if c == cat]
                rows = [row_basic(r, e) for r, e in winners]
                body.append(_html_table(headers, rows))

        body.append("<h2 id='awards_1x'>入賞（1X：各エリア1位）</h2>")
        if not rows_out:
            body.append("<p class='small'>対象局なし</p>")
        else:
            headers = ["順位", "コール", "部門", "運用地", "有効QSO", "素点", "マルチ", "総得点"]
            for d in sorted({d for d, _, _ in rows_out}):
                body.append(f"<h3>{d}エリア</h3>")
                winners = [(r, e) for (dd, r, e) in rows_out if dd == d]
                rows = [row_basic(r, e) for r, e in winners]
                body.append(_html_table(headers, rows))

        body.append("<h2 id='overall'>総合結果</h2>")
        headers = ["順位", "コール", "部門", "運用地", "有効QSO", "素点", "マルチ", "総得点"]
        rows = [row_basic(r, e) for r, e in overall_ranked]
        body.append(_html_table(headers, rows))

        body.append("<h2 id='bycat'>部門別結果</h2>")
        cats_all = sorted({(e.category or "") for e in entries_all if (e.category or "").strip()})
        for cat in cats_all:
            es = [e for e in entries_all if (e.category or "") == cat]
            es_sorted = sorted(es, key=_rank_sort_key)
            ranked = _competition_ranks(es_sorted)
            body.append(f"<h3>{_h(category_display(cat))}</h3>")
            rows = [row_basic(r, e) for r, e in ranked]
            body.append(_html_table(headers, rows))

        body.append("<h2 id='comments'>コメント一覧</h2>")
        coms = [(e.callsign, (e.comments or "").strip()) for e in entries_all if (e.comments or "").strip()]
        if not coms:
            body.append("<p class='small'>コメントなし</p>")
        else:
            coms.sort(key=lambda x: x[0])
            body.append("<table class='tbl'><thead><tr><th>コール</th><th>コメント</th></tr></thead><tbody>" +
                        "".join([f"<tr><td>{_h(cs)}</td><td>{_h(c).replace(chr(10), '<br>')}</td></tr>" for cs, c in coms]) +
                        "</tbody></table>")

        html_out = _html_page("コンテスト結果（発表用）", "\n".join(body))
        path_out = os.path.join(out_dir, "publish_results.html")
        try:
            with open(path_out, "w", encoding="utf-8", newline="\n") as f:
                f.write(html_out)
            self.status_var.set(f"発表HTML出力: {path_out}")
            messagebox.showinfo("発表HTML", f"出力しました。\n\n{path_out}\n\nブラウザで開いて印刷すればPDFにもできます。")
        except Exception as ex:
            messagebox.showerror("発表HTML", str(ex))

    # -----------------------------
    # ★新機能：賞状/参加証 PDF 出力
    # -----------------------------

    def on_export_award_pdfs(self) -> None:
        if not self.entries:
            messagebox.showinfo("賞状PDF", "出力するデータがありません。")
            return

        out_dir = filedialog.askdirectory(
            initialdir=self.folder_var.get() or os.getcwd(),
            title="保存先フォルダを選択（入賞局の賞状PDFを出力）"
        )
        if not out_dir:
            return

        folder = self.folder_var.get().strip()
        bg_path = _bg_path_from_folder(folder, DEFAULT_CERT_BG)
        if not os.path.isfile(bg_path):
            messagebox.showwarning(
                "背景が見つかりません",
                f"賞状背景 {DEFAULT_CERT_BG} がフォルダに見つかりません。\n\n{bg_path}\n\n背景なしで生成します。"
            )
            bg_path = ""

        all_entries = [e for e in self.entries.values() if not e.is_checklog]
        rows_in, rows_out = build_award_lists(all_entries)

        saved = 0
        errors: List[str] = []

        # 1F/1P/1Q/SWL
        for cat, rank, e in rows_in:
            try:
                fn = f"award_{_safe_filename(e.callsign)}_{cat}_R{rank}.pdf"
                path = os.path.join(out_dir, fn)
                generate_award_pdf_one(
                    out_path=path,
                    bg_path=bg_path,
                    callsign=e.callsign,
                    year=CONTEST_YEAR,
                    category_code=cat,
                    rank=rank,
                    total_score=int(e.recalced_total),
                )
                saved += 1
            except Exception as ex:
                errors.append(f"{e.callsign}: {ex}")

        # 1X 各エリア
        for area, rank, e in rows_out:
            try:
                fn = f"award_{_safe_filename(e.callsign)}_1X_area{area}_R{rank}.pdf"
                path = os.path.join(out_dir, fn)
                generate_award_pdf_one(
                    out_path=path,
                    bg_path=bg_path,
                    callsign=e.callsign,
                    year=CONTEST_YEAR,
                    category_code="1X",
                    rank=rank,
                    total_score=int(e.recalced_total),
                )
                saved += 1
            except Exception as ex:
                errors.append(f"{e.callsign}: {ex}")

        msg = f"賞状PDF出力 完了: {saved}枚"
        if errors:
            msg += f" / エラー={len(errors)}（詳細はコンソール）"
            print("---- award pdf errors ----")
            for x in errors[:200]:
                print(x)

        self.status_var.set(msg)
        messagebox.showinfo("賞状PDF", msg)

    def on_export_entry_pdfs(self) -> None:
        if not self.entries:
            messagebox.showinfo("参加証PDF", "出力するデータがありません。")
            return

        out_dir = filedialog.askdirectory(
            initialdir=self.folder_var.get() or os.getcwd(),
            title="保存先フォルダを選択（参加者全員の参加証PDFを出力）"
        )
        if not out_dir:
            return

        folder = self.folder_var.get().strip()
        bg_path = _bg_path_from_folder(folder, DEFAULT_ENTRY_BG)
        if not os.path.isfile(bg_path):
            messagebox.showwarning(
                "背景が見つかりません",
                f"参加証背景 {DEFAULT_ENTRY_BG} がフォルダに見つかりません。\n\n{bg_path}\n\n背景なしで生成します。"
            )
            bg_path = ""

        saved = 0
        errors: List[str] = []

        for e in sorted(self.entries.values(), key=lambda x: x.callsign):
            if e.is_checklog:
                continue
            try:
                fn = f"entry_{_safe_filename(e.callsign)}.pdf"
                path = os.path.join(out_dir, fn)
                generate_entry_pdf_one(
                    out_path=path,
                    bg_path=bg_path,
                    callsign=e.callsign,
                    year=CONTEST_YEAR,
                    category_code=(e.category or "").strip(),
                    total_score=int(e.recalced_total),
                )
                saved += 1
            except Exception as ex:
                errors.append(f"{e.callsign}: {ex}")

        msg = f"参加証PDF出力 完了: {saved}枚"
        if errors:
            msg += f" / エラー={len(errors)}（詳細はコンソール）"
            print("---- entry pdf errors ----")
            for x in errors[:200]:
                print(x)

        self.status_var.set(msg)
        messagebox.showinfo("参加証PDF", msg)


class ManualEditDialog(tk.Toplevel):
    def __init__(self, master: tk.Tk, entry: StationEntry, on_saved=None) -> None:
        super().__init__(master)
        self.entry = entry
        self.on_saved = on_saved
        self.title(f"手動訂正: {entry.callsign}")
        self.geometry("560x360")
        self.resizable(False, False)

        self.enabled_var = tk.BooleanVar(value=bool(entry.manual_enabled))
        self.qso_var = tk.StringVar(value="" if entry.manual_qso is None else str(entry.manual_qso))
        self.pts_var = tk.StringVar(value="" if entry.manual_pts is None else str(entry.manual_pts))
        self.mult_var = tk.StringVar(value="" if entry.manual_mult is None else str(entry.manual_mult))
        self.total_var = tk.StringVar(value="" if entry.manual_total is None else str(entry.manual_total))
        self.note_var = tk.StringVar(value=entry.manual_note or "")
        self.opplace_var = tk.StringVar(value=entry.manual_opplace or "")

        frm = ttk.Frame(self)
        frm.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Checkbutton(frm, text="手動訂正を有効にする（再計算値/運用地を上書き）", variable=self.enabled_var)\
            .grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 12))

        def add_row(r, label, var, width=20):
            ttk.Label(frm, text=label).grid(row=r, column=0, sticky="w", pady=6)
            ttk.Entry(frm, textvariable=var, width=width).grid(row=r, column=1, sticky="w", pady=6)

        add_row(1, "QSO数（空=上書きしない）", self.qso_var)
        add_row(2, "素点（空=上書きしない）", self.pts_var)
        add_row(3, "マルチ（空=上書きしない）", self.mult_var)
        add_row(4, "総得点（空=素点×マルチ）", self.total_var)
        add_row(5, "運用地（空=上書きしない）", self.opplace_var, width=45)

        ttk.Label(frm, text="メモ（任意）").grid(row=6, column=0, sticky="w", pady=(12, 6))
        ttk.Entry(frm, textvariable=self.note_var, width=45).grid(row=6, column=1, sticky="w", pady=(12, 6))

        btns = ttk.Frame(frm)
        btns.grid(row=7, column=0, columnspan=2, sticky="e", pady=(18, 0))
        ttk.Button(btns, text="キャンセル", command=self.destroy).pack(side="right", padx=6)
        ttk.Button(btns, text="保存", command=self._save).pack(side="right", padx=6)

        hint = ttk.Label(frm, text="※ 運用地の表示だけ直したい局は「運用地」に正しい市区町村を入れて保存できます。")
        hint.grid(row=8, column=0, columnspan=2, sticky="w", pady=(14, 0))

    def _parse_opt_int(self, s: str) -> Optional[int]:
        s = (s or "").strip().replace(",", "")
        if s == "":
            return None
        if not re.fullmatch(r"\d+", s):
            raise ValueError("数字のみ入力してください（空欄はOK）")
        return int(s)

    def _save(self) -> None:
        try:
            enabled = bool(self.enabled_var.get())
            qso = self._parse_opt_int(self.qso_var.get())
            pts = self._parse_opt_int(self.pts_var.get())
            mult = self._parse_opt_int(self.mult_var.get())
            total = self._parse_opt_int(self.total_var.get())
            note = (self.note_var.get() or "").strip()
            opplace = (self.opplace_var.get() or "").strip()

            self.entry.manual_enabled = enabled
            self.entry.manual_qso = qso
            self.entry.manual_pts = pts
            self.entry.manual_mult = mult
            self.entry.manual_total = total
            self.entry.manual_note = note
            self.entry.manual_opplace = opplace

            recalc_entry(self.entry)

            if self.on_saved:
                self.on_saved()
            self.destroy()
        except Exception as ex:
            messagebox.showerror("入力エラー", str(ex))


class DetailWindow(tk.Toplevel):
    def __init__(self, master: tk.Tk, entry: StationEntry) -> None:
        super().__init__(master)
        self.entry = entry
        self.title(f"詳細: {entry.callsign}")
        self.geometry("1200x600")

        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=8)

        s1 = f"コール: {entry.callsign}    部門: {category_display(entry.category)}"
        s2 = f"運用地: {entry.opplace}"
        cl = f"申告: QSO={entry.claimed_qso} Pts={entry.claimed_pts} Mult={entry.claimed_mult} Total={entry.claimed_total}"
        rc = f"再計算: QSO={entry.recalced_qso} Pts={entry.recalced_pts} Mult={entry.recalced_mult} Total={entry.recalced_total}"
        rs = f"判定: {'CHECKLOG' if entry.is_checklog else ('OK' if entry.match else '差あり')}    推定: {entry.reason}"

        ttk.Label(top, text=s1).pack(anchor="w")
        ttk.Label(top, text=s2).pack(anchor="w")
        ttk.Label(top, text=cl).pack(anchor="w")
        ttk.Label(top, text=rc).pack(anchor="w")
        ttk.Label(top, text=rs, foreground=("red" if (not entry.match and not entry.is_checklog) else "black")).pack(anchor="w")

        frame = ttk.Frame(self)
        frame.pack(fill="both", expand=True, padx=10, pady=8)

        cols = ("date", "time", "band", "mode", "call", "rcvd", "multkey", "pts", "dup")
        tree = ttk.Treeview(frame, columns=cols, show="headings")
        tree.heading("date", text="DATE")
        tree.heading("time", text="TIME")
        tree.heading("band", text="BAND")
        tree.heading("mode", text="MODE")
        tree.heading("call", text="CALL")
        tree.heading("rcvd", text="RCVD")
        tree.heading("multkey", text="MULT(新規のみ表示)")
        tree.heading("pts", text="PTS")
        tree.heading("dup", text="DUP?")

        tree.column("date", width=95, anchor="w")
        tree.column("time", width=70, anchor="w")
        tree.column("band", width=55, anchor="center")
        tree.column("mode", width=55, anchor="center")
        tree.column("call", width=120, anchor="w")
        tree.column("rcvd", width=90, anchor="e")
        tree.column("multkey", width=120, anchor="e")
        tree.column("pts", width=70, anchor="e")
        tree.column("dup", width=70, anchor="center")

        vsb = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        hsb = ttk.Scrollbar(frame, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")

        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)

        tree.tag_configure("dup", foreground="red")

        seen_mult = set()
        for q in entry.qsos:
            ex = _canon_exchange(q.rcvd_exch)
            is_new = False
            if (not q.dup) and q.pts > 0 and ex:
                if ex not in seen_mult:
                    is_new = True
                    seen_mult.add(ex)
            mult_disp = ex if is_new else "-"
            tree.insert(
                "", "end",
                values=(q.date, q.time, q.band_mhz, q.mode, q.worked_call, ex, mult_disp, q.pts, "YES" if q.dup else ""),
                tags=("dup",) if q.dup else ()
            )


# -----------------------------
# main
# -----------------------------

def main() -> None:
    try:
        app = App()
        app.mainloop()
    except Exception:
        traceback.print_exc()
        messagebox.showerror("致命的エラー", traceback.format_exc())


if __name__ == "__main__":
    main()
