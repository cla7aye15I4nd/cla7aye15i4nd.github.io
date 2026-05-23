from __future__ import annotations

import shutil
from collections import defaultdict
from pathlib import Path
from typing import Any

import frontmatter
import yaml

from site_builder.markdown import convert as markdown_convert
from site_builder.markdown import extract_title
from site_builder.models import BuildResult, Page, Post, SiteConfig, SiteContext
from site_builder.renderer import Renderer


class SiteBuilder:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.config = self._load_config(root)
        self.renderer = Renderer(self.config.template_dir)

    @staticmethod
    def _load_config(root: Path) -> SiteConfig:
        config_path = root / "site.yaml"
        with config_path.open("r", encoding="utf-8") as f:
            raw = yaml.safe_load(f) or {}
        return SiteConfig.from_dict(root, raw)

    def build(self) -> BuildResult:
        result = BuildResult()
        self._prepare_output()

        context = SiteContext(config=self.config, data=self._load_data())

        posts = self._load_posts(result)
        self._link_translations(posts)
        context.posts = sorted(posts, key=lambda p: p.date, reverse=True)

        pages = self._load_pages(result)
        context.pages = pages

        for page in pages:
            try:
                self._render_page(page, context)
                result.pages += 1
            except Exception as exc:
                result.errors.append(f"page {page.source.name}: {exc}")

        for post in posts:
            try:
                self._render_post(post, context)
                result.posts += 1
            except Exception as exc:
                result.errors.append(f"post {post.source.name}: {exc}")

        if posts:
            try:
                self._render_archive(posts, context)
            except Exception as exc:
                result.errors.append(f"archive: {exc}")

        result.copied = self._copy_assets()
        return result

    def _prepare_output(self) -> None:
        out = self.config.output_dir
        if out.exists():
            shutil.rmtree(out)
        out.mkdir(parents=True, exist_ok=True)
        (out / "blog").mkdir(exist_ok=True)

    def _load_data(self) -> dict[str, Any]:
        data_dir = self.config.content_dir / "data"
        if not data_dir.exists():
            return {}
        merged: dict[str, Any] = {}
        for path in sorted(data_dir.glob("*.yaml")):
            with path.open("r", encoding="utf-8") as f:
                merged[path.stem] = yaml.safe_load(f)
        return merged

    def _load_posts(self, result: BuildResult) -> list[Post]:
        posts_dir = self.config.content_dir / "blog"
        if not posts_dir.exists():
            return []
        posts: list[Post] = []
        for path in sorted(posts_dir.glob("*.md")):
            try:
                post = self._parse_post(path)
            except Exception as exc:
                result.errors.append(f"post {path.name}: {exc}")
                continue
            if post is None:
                result.skipped += 1
                continue
            posts.append(post)
        return posts

    def _parse_post(self, path: Path) -> Post | None:
        parsed = frontmatter.load(path)
        meta: dict[str, Any] = dict(parsed.metadata)
        raw_tags = meta.get("tags") or []
        if not isinstance(raw_tags, list):
            raise ValueError(f"{path}: tags must be a list")
        tags = [str(t).strip().lower() for t in raw_tags]
        if "unfinished" in tags:
            return None

        body = parsed.content
        if not meta.get("title"):
            title = extract_title(body)
            if title:
                meta["title"] = title

        html, toc = markdown_convert(body)
        return Post.from_frontmatter(
            source=path,
            meta=meta,
            content_html=html,
            toc_html=toc,
            default_lang=self.config.default_lang,
        )

    @staticmethod
    def _link_translations(posts: list[Post]) -> None:
        by_slug: dict[str, list[Post]] = defaultdict(list)
        for post in posts:
            by_slug[post.slug].append(post)
        for group in by_slug.values():
            if len(group) < 2:
                continue
            for post in group:
                post.translations = {p.lang: p for p in group if p.lang != post.lang}

    def _load_pages(self, result: BuildResult) -> list[Page]:
        pages_dir = self.config.content_dir / "pages"
        if not pages_dir.exists():
            return []
        pages: list[Page] = []
        for path in sorted(pages_dir.iterdir()):
            if not path.is_file():
                continue
            try:
                page = self._parse_page(path)
            except Exception as exc:
                result.errors.append(f"page {path.name}: {exc}")
                continue
            pages.append(page)
        return pages

    def _parse_page(self, path: Path) -> Page:
        suffix = path.suffix.lower()
        name = path.stem
        if suffix == ".yaml":
            with path.open("r", encoding="utf-8") as f:
                meta = yaml.safe_load(f) or {}
            if not isinstance(meta, dict):
                raise ValueError("page yaml must be a mapping")
            template = str(meta.get("template") or f"{name}.html")
            output = Path(str(meta.get("output") or f"{name}.html"))
            return Page(
                name=name,
                source=path,
                output=output,
                template=template,
                meta=meta,
                content_html=None,
            )
        if suffix == ".md":
            parsed = frontmatter.load(path)
            meta = dict(parsed.metadata)
            if not meta.get("title"):
                meta["title"] = extract_title(parsed.content) or name
            html, _ = markdown_convert(parsed.content)
            template = str(meta.get("template") or "page.html")
            output = Path(str(meta.get("output") or f"{name}.html"))
            return Page(
                name=name,
                source=path,
                output=output,
                template=template,
                meta=meta,
                content_html=html,
            )
        if suffix == ".html":
            verbatim = path.read_text(encoding="utf-8")
            return Page(
                name=name,
                source=path,
                output=Path(f"{name}.html"),
                template="",
                meta={},
                content_html=None,
                verbatim_html=verbatim,
            )
        raise ValueError(f"unsupported page type: {path.name}")

    def _render_page(self, page: Page, context: SiteContext) -> None:
        out_path = self.config.output_dir / page.output
        out_path.parent.mkdir(parents=True, exist_ok=True)
        if page.verbatim_html is not None:
            out_path.write_text(page.verbatim_html, encoding="utf-8")
            return
        html = self.renderer.render_page(page, context)
        out_path.write_text(html, encoding="utf-8")

    def _render_post(self, post: Post, context: SiteContext) -> None:
        out_path = self.config.output_dir / post.output
        out_path.parent.mkdir(parents=True, exist_ok=True)
        html = self.renderer.render_post(post, context)
        out_path.write_text(html, encoding="utf-8")

    def _render_archive(self, posts: list[Post], context: SiteContext) -> None:
        out_path = self.config.output_dir / "blog" / "index.html"
        html = self.renderer.render_archive(posts, context)
        out_path.write_text(html, encoding="utf-8")

    def _copy_assets(self) -> int:
        copied = 0
        ignore = shutil.ignore_patterns(".DS_Store", "*.swp", "Thumbs.db")
        static_src = self.config.static_dir
        if static_src.exists():
            shutil.copytree(
                static_src,
                self.config.output_dir / "static",
                dirs_exist_ok=True,
                ignore=ignore,
            )
            copied += 1
        for src in self.config.copy_dirs:
            if src.exists():
                shutil.copytree(
                    src,
                    self.config.output_dir / src.name,
                    dirs_exist_ok=True,
                    ignore=ignore,
                )
                copied += 1
        for src in self.config.copy_files:
            if src.exists():
                shutil.copy2(src, self.config.output_dir / src.name)
                copied += 1
        return copied
