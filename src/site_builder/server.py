from __future__ import annotations

import http.server
import os
import threading
from collections.abc import Iterable
from pathlib import Path
from typing import Any

from site_builder.builder import SiteBuilder

_LIVERELOAD_PATH = "/__livereload"
_LIVERELOAD_SCRIPT = (
    b"<script>(function(){try{var es=new EventSource('"
    + _LIVERELOAD_PATH.encode()
    + b"');es.addEventListener('reload',function(){window.location.reload();});}"
    b"catch(e){}})();</script>"
)


class _ReloadBroker:
    def __init__(self) -> None:
        self._cond = threading.Condition()
        self._generation = 0

    @property
    def generation(self) -> int:
        with self._cond:
            return self._generation

    def notify(self) -> None:
        with self._cond:
            self._generation += 1
            self._cond.notify_all()

    def wait(self, last_seen: int, timeout: float) -> int:
        with self._cond:
            self._cond.wait_for(lambda: self._generation > last_seen, timeout=timeout)
            return self._generation


def _make_handler(
    broker: _ReloadBroker, directory: str
) -> type[http.server.SimpleHTTPRequestHandler]:
    class _Handler(http.server.SimpleHTTPRequestHandler):
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            super().__init__(*args, directory=directory, **kwargs)

        def log_message(self, format: str, *args: Any) -> None:
            if self.path.startswith(_LIVERELOAD_PATH):
                return
            super().log_message(format, *args)

        def handle_one_request(self) -> None:
            try:
                super().handle_one_request()
            except (ConnectionResetError, BrokenPipeError, ConnectionAbortedError, TimeoutError):
                self.close_connection = True

        def do_GET(self) -> None:
            if self.path.split("?", 1)[0] == _LIVERELOAD_PATH:
                self._handle_livereload()
                return
            path = self.translate_path(self.path)
            if os.path.isdir(path):
                for index in ("index.html", "index.htm"):
                    candidate = os.path.join(path, index)
                    if os.path.isfile(candidate):
                        path = candidate
                        break
            if path.endswith(".html") and os.path.isfile(path):
                self._send_html_with_reload(path)
                return
            super().do_GET()

        def _send_html_with_reload(self, path: str) -> None:
            try:
                with open(path, "rb") as f:
                    body = f.read()
            except OSError:
                self.send_error(404)
                return
            idx = body.lower().rfind(b"</body>")
            body = body[:idx] + _LIVERELOAD_SCRIPT + body[idx:] if idx >= 0 else body + _LIVERELOAD_SCRIPT
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _handle_livereload(self) -> None:
            self.close_connection = True
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-cache")
            self.send_header("Connection", "close")
            self.send_header("X-Accel-Buffering", "no")
            self.end_headers()
            last_seen = broker.generation
            try:
                self.wfile.write(b"retry: 1000\n\n")
                self.wfile.flush()
                while True:
                    new_gen = broker.wait(last_seen, timeout=15.0)
                    if new_gen > last_seen:
                        self.wfile.write(b"event: reload\ndata: 1\n\n")
                        self.wfile.flush()
                        last_seen = new_gen
                    else:
                        self.wfile.write(b": ping\n\n")
                        self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError, OSError):
                return

    return _Handler


def _build_once(root: Path) -> bool:
    builder = SiteBuilder(root)
    result = builder.build()
    if result.errors:
        for err in result.errors:
            print(f"  error: {err}")
        return False
    print(f"  built {result.pages} page(s), {result.posts} post(s)")
    return True


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
    broker = _ReloadBroker()
    handler_class = _make_handler(broker, str(out_dir))

    class _Server(http.server.ThreadingHTTPServer):
        allow_reuse_address = True
        daemon_threads = True

    server = _Server((host, port), handler_class)
    print(f"==> serving http://{host}:{port}  (Ctrl-C to stop)")
    print("==> live-reload enabled")

    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()

    try:
        for _changes in watch(*_watch_paths(root)):
            print("==> change detected, rebuilding")
            if _build_once(root):
                broker.notify()
    except KeyboardInterrupt:
        print("\n==> shutting down")
    finally:
        server.shutdown()
