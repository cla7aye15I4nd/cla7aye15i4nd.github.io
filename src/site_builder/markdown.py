from __future__ import annotations

import re

import markdown


def _normalize_list_indentation(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    in_code = False
    for line in lines:
        if line.strip().startswith("```"):
            in_code = not in_code
            out.append(line)
            continue
        if in_code:
            out.append(line)
            continue
        stripped = line.lstrip(" ")
        is_list_item = stripped.startswith(("-", "*", "+")) or (
            stripped and stripped[0].isdigit() and "." in stripped[:4]
        )
        if is_list_item:
            indent = len(line) - len(stripped)
            if indent > 0:
                out.append(" " * ((indent // 2) * 4) + stripped)
                continue
        out.append(line)
    return "\n".join(out)


_CALLOUT_RE = re.compile(
    r">\s*\[!(NOTE|WARNING|IMPORTANT|TIP|CAUTION)\](?: ([^\n>]+?))?\s*\n((?:>.*\n?)+)",
    re.MULTILINE | re.IGNORECASE,
)


def _convert_github_callouts(text: str) -> str:
    def repl(match: re.Match[str]) -> str:
        kind = match.group(1).lower()
        title = match.group(2).strip() if match.group(2) else kind.upper()
        body = re.sub(r"^>\s*", "", match.group(3).strip(), flags=re.MULTILINE)
        body = "\n".join("    " + line if line else "" for line in body.split("\n"))
        return f'!!! {kind} "{title}"\n{body}'

    return _CALLOUT_RE.sub(repl, text)


def _add_blank_lines_before_lists(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    in_code = False
    prev = ""
    for line in lines:
        if line.strip().startswith("```"):
            in_code = not in_code
            out.append(line)
            prev = line
            continue
        if in_code:
            out.append(line)
            prev = line
            continue
        stripped = line.lstrip()
        prev_is_text = prev and not prev.strip().startswith(("```", "-", "*", "+", "#"))
        starts_list = stripped and (
            stripped.startswith(("-", "*", "+"))
            or (stripped[0].isdigit() and "." in stripped[:4])
        )
        if prev_is_text and starts_list:
            out.append("")
        out.append(line)
        prev = line
    return "\n".join(out)


def preprocess(text: str) -> str:
    text = _convert_github_callouts(text)
    text = _normalize_list_indentation(text)
    text = _add_blank_lines_before_lists(text)
    return text


def _build_markdown() -> markdown.Markdown:
    return markdown.Markdown(
        extensions=[
            "pymdownx.superfences",
            "pymdownx.arithmatex",
            "pymdownx.magiclink",
            "pymdownx.betterem",
            "pymdownx.tasklist",
            "pymdownx.emoji",
            "pymdownx.highlight",
            "tables",
            "fenced_code",
            "sane_lists",
            "attr_list",
            "def_list",
            "admonition",
            "toc",
        ],
        extension_configs={
            "pymdownx.highlight": {
                "css_class": "highlight",
                "use_pygments": True,
                "pygments_style": "github-dark",
                "linenums": False,
            },
            "pymdownx.arithmatex": {"generic": True},
            "toc": {
                "permalink": True,
                "toc_depth": 5,
                "baselevel": 2,
                "title": "",
            },
        },
    )


def convert(text: str) -> tuple[str, str]:
    md = _build_markdown()
    html = md.convert(preprocess(text))
    toc = getattr(md, "toc", "")
    return html, toc


_FIRST_H1_RE = re.compile(r"^#\s+(.+)$", re.MULTILINE)


def extract_title(text: str) -> str | None:
    match = _FIRST_H1_RE.search(text)
    if match:
        return match.group(1).strip()
    return None
