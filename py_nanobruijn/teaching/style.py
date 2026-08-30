"""ANSI 颜色辅助：教学 REPL 的可选彩色输出（零依赖）。"""
from __future__ import annotations

import os
import sys

_CODES = {
    "red": "\x1b[31m",
    "green": "\x1b[32m",
    "yellow": "\x1b[33m",
    "blue": "\x1b[34m",
    "magenta": "\x1b[35m",
    "cyan": "\x1b[36m",
    "gray": "\x1b[90m",
    "bold": "\x1b[1m",
}
_RESET = "\x1b[0m"


def colorize(text: str, color: str) -> str:
    code = _CODES.get(color)
    if code is None:
        return text
    return f"{code}{text}{_RESET}"


def color_enabled(flag: bool | None = None) -> bool:
    """flag=None → 自动：TTY 检测 + NO_COLOR 环境变量。"""
    if flag is not None:
        return flag
    if os.environ.get("NO_COLOR"):
        return False
    return bool(getattr(sys.stdout, "isatty", lambda: False)())