from __future__ import annotations

from ..errors import ParseError

KEYWORDS = {"fun", "forall", "Type", "Prop", "Sort"}
SYMBOLS = set("():,@=>∀{}")

Token = tuple[str, object]


def tokenize(text: str) -> list[Token]:
    tokens: list[Token] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if c.isdigit():
            j = i
            while j < n and text[j].isdigit():
                j += 1
            tokens.append(("int", int(text[i:j])))
            i = j
            continue
        if c == '-':
            if i + 1 < n and text[i + 1] == '>':
                tokens.append(("sym", "->"))
                i += 2
                continue
            raise ParseError(f"unexpected character {c!r} at position {i}")
        if c == '=':
            if i + 1 < n and text[i + 1] == '>':
                tokens.append(("sym", "=>"))
                i += 2
                continue
            raise ParseError(f"unexpected character {c!r} at position {i}")
        if c == '∀':
            tokens.append(("sym", "∀"))
            i += 1
            continue
        if c in SYMBOLS:
            tokens.append(("sym", c))
            i += 1
            continue
        if c.isalpha() or c == '_':
            j = i
            while j < n and (text[j].isalnum() or text[j] in "._'"):
                j += 1
            word = text[i:j]
            if word in KEYWORDS:
                tokens.append(("kw", word))
            else:
                tokens.append(("name", word))
            i = j
            continue
        raise ParseError(f"unexpected character {c!r} at position {i}")
    return tokens