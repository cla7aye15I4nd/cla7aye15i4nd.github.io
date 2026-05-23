from __future__ import annotations

from collections import defaultdict
from pathlib import Path

from jinja2 import ChainableUndefined, Environment, FileSystemLoader, select_autoescape

from site_builder.models import Page, Post, SiteContext


class Renderer:
    def __init__(self, template_dir: Path) -> None:
        self.env = Environment(
            loader=FileSystemLoader(str(template_dir)),
            autoescape=select_autoescape(["html"]),
            undefined=ChainableUndefined,
            trim_blocks=True,
            lstrip_blocks=True,
        )

    def render_page(self, page: Page, context: SiteContext) -> str:
        template = self.env.get_template(page.template)
        return template.render(
            page=page,
            **context.template_globals(),
        )

    def render_post(self, post: Post, context: SiteContext) -> str:
        template = self.env.get_template("article.html")
        return template.render(
            post=post,
            **context.template_globals(),
        )

    def render_archive(self, posts: list[Post], context: SiteContext) -> str:
        groups = self._group_by_slug(posts)
        sorted_posts = sorted(
            (group[0] for group in groups),
            key=lambda p: p.date,
            reverse=True,
        )
        by_tag = self._group_by_tag(sorted_posts)
        template = self.env.get_template("archive.html")
        return template.render(
            posts=sorted_posts,
            posts_by_tag=by_tag,
            **context.template_globals(),
        )

    @staticmethod
    def _group_by_slug(posts: list[Post]) -> list[list[Post]]:
        bucket: dict[str, list[Post]] = defaultdict(list)
        for post in posts:
            bucket[post.slug].append(post)
        return list(bucket.values())

    @staticmethod
    def _group_by_tag(posts: list[Post]) -> dict[str, list[Post]]:
        bucket: dict[str, list[Post]] = defaultdict(list)
        for post in posts:
            for tag in post.tags:
                bucket[tag].append(post)
        for tag in bucket:
            bucket[tag].sort(key=lambda p: p.date, reverse=True)
        return dict(sorted(bucket.items()))
