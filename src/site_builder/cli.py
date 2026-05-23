from __future__ import annotations

import argparse
import sys
from pathlib import Path

from site_builder.builder import SiteBuilder


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="site", description="Static site builder")
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="Project root")
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("build", help="Build the site into dist/")

    p_serve = sub.add_parser("serve", help="Build, serve, and rebuild on change")
    p_serve.add_argument("--host", default="127.0.0.1")
    p_serve.add_argument("--port", type=int, default=8000)

    sub.add_parser("clean", help="Remove the output directory")

    args = parser.parse_args(argv)
    root: Path = args.root.resolve()

    if args.command == "build":
        builder = SiteBuilder(root)
        result = builder.build()
        if result.errors:
            for err in result.errors:
                print(f"error: {err}", file=sys.stderr)
            return 1
        print(
            f"built {result.pages} page(s), {result.posts} post(s), "
            f"copied {result.copied} asset group(s), skipped {result.skipped}"
        )
        return 0

    if args.command == "serve":
        from site_builder.server import serve

        serve(root, host=args.host, port=args.port)
        return 0

    if args.command == "clean":
        out = root / "dist"
        if out.exists():
            import shutil

            shutil.rmtree(out)
            print(f"removed {out}")
        return 0

    parser.error("unknown command")
    return 2
