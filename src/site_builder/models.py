from __future__ import annotations

from dataclasses import dataclass, field
from datetime import date as date_cls
from datetime import datetime
from pathlib import Path
from typing import Any


@dataclass(slots=True)
class SiteConfig:
    title: str
    author: str
    domain: str
    analytics: dict[str, Any]
    default_lang: str
    content_dir: Path
    template_dir: Path
    static_dir: Path
    output_dir: Path
    copy_dirs: list[Path]
    copy_files: list[Path]

    @classmethod
    def from_dict(cls, root: Path, raw: dict[str, Any]) -> SiteConfig:
        return cls(
            title=str(raw.get("title", "")),
            author=str(raw.get("author", "")),
            domain=str(raw.get("domain", "")),
            analytics=dict(raw.get("analytics") or {}),
            default_lang=str(raw.get("default_lang", "en")),
            content_dir=root / str(raw.get("content_dir", "content")),
            template_dir=root / str(raw.get("template_dir", "templates")),
            static_dir=root / str(raw.get("static_dir", "static")),
            output_dir=root / str(raw.get("output_dir", "dist")),
            copy_dirs=[root / p for p in raw.get("copy_dirs", [])],
            copy_files=[root / p for p in raw.get("copy_files", [])],
        )


def _normalize_date(value: Any) -> str:
    if isinstance(value, (datetime, date_cls)):
        return value.strftime("%Y-%m-%d")
    if isinstance(value, str):
        datetime.strptime(value, "%Y-%m-%d")
        return value
    raise ValueError(f"Invalid date value: {value!r}")


@dataclass(slots=True)
class Post:
    slug: str
    lang: str
    source: Path
    output: Path
    url: str
    title: str
    date: str
    tags: list[str]
    description: str | None
    content_html: str
    toc_html: str
    translations: dict[str, Post] = field(default_factory=dict)

    @classmethod
    def from_frontmatter(
        cls,
        *,
        source: Path,
        meta: dict[str, Any],
        content_html: str,
        toc_html: str,
        default_lang: str,
    ) -> Post:
        slug = str(meta.get("slug") or _slug_from_filename(source))
        lang = str(meta.get("lang") or _lang_from_filename(source, default_lang))
        date = _normalize_date(meta.get("date"))
        title = str(meta.get("title") or _title_from_filename(source))
        tags_raw = meta.get("tags") or []
        if not isinstance(tags_raw, list):
            raise ValueError(f"{source}: tags must be a list")
        tags = [str(t).strip().lower() for t in tags_raw]
        description = meta.get("description")
        if description is not None:
            description = str(description)

        output_name = f"{slug}.html" if lang == default_lang else f"{slug}.{lang}.html"
        return cls(
            slug=slug,
            lang=lang,
            source=source,
            output=Path("blog") / output_name,
            url=f"{output_name}",
            title=title,
            date=date,
            tags=tags,
            description=description,
            content_html=content_html,
            toc_html=toc_html,
        )


@dataclass(slots=True)
class Page:
    name: str
    source: Path
    output: Path
    template: str
    meta: dict[str, Any]
    content_html: str | None
    verbatim_html: str | None = None


def _slug_from_filename(path: Path) -> str:
    stem = path.stem
    if "." in stem:
        return stem.split(".", 1)[0]
    return stem


def _lang_from_filename(path: Path, default_lang: str) -> str:
    stem = path.stem
    if "." in stem:
        return stem.split(".", 1)[1]
    return default_lang


def _title_from_filename(path: Path) -> str:
    return _slug_from_filename(path).replace("-", " ").replace("_", " ").title()


@dataclass(slots=True)
class SiteContext:
    config: SiteConfig
    data: dict[str, Any]
    pages: list[Page] = field(default_factory=list)
    posts: list[Post] = field(default_factory=list)

    def template_globals(self) -> dict[str, Any]:
        return {
            "site": {
                "title": self.config.title,
                "author": self.config.author,
                "domain": self.config.domain,
                "analytics": self.config.analytics,
                "default_lang": self.config.default_lang,
                "data": self.data,
            },
        }


@dataclass(slots=True)
class BuildResult:
    pages: int = 0
    posts: int = 0
    skipped: int = 0
    copied: int = 0
    errors: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.errors
