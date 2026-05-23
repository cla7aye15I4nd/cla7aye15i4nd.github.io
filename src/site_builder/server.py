from __future__ import annotations

import functools
import http.server
import socketserver
import threading
from collections.abc import Iterable
from pathlib import Path

from site_builder.builder import SiteBuilder


def _build_once(root: Path) -> None:
    builder = SiteBuilder(root)
    result = builder.build()
    if result.errors:
        for err in result.errors:
            print(f"  error: {err}")
        return
    print(f"  built {result.pages} page(s), {result.posts} post(s)")


def _watch_paths(root: Path) -> Iterable[Path]:
    candidates = [
        root / "content",
        root / "templates",
        root / "static",
        root / "site.yaml",
    ]
    return [p for p in candidates if p.exists()]


def serve(root: Path, *, host: str = "127.0.0.1", port: int = 8000) -> None:
    from watchfiles import watch

    print("==> initial build")
    _build_once(root)

    out_dir = (root / "dist").resolve()

    handler = functools.partial(http.server.SimpleHTTPRequestHandler, directory=str(out_dir))

    class _Server(socketserver.ThreadingTCPServer):
        allow_reuse_address = True
        daemon_threads = True

    server = _Server((host, port), handler)
    print(f"==> serving http://{host}:{port}  (Ctrl-C to stop)")

    def _serve() -> None:
        server.serve_forever()

    thread = threading.Thread(target=_serve, daemon=True)
    thread.start()

    try:
        for _changes in watch(*_watch_paths(root)):
            print("==> change detected, rebuilding")
            _build_once(root)
    except KeyboardInterrupt:
        print("\n==> shutting down")
    finally:
        server.shutdown()
