#!/usr/bin/env python3
"""Dev server with caching disabled (so edits always show on reload)."""
import functools, http.server, sys
class Handler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header('Cache-Control', 'no-store')
        super().end_headers()
port = int(sys.argv[1]) if len(sys.argv) > 1 else 8123
http.server.test(HandlerClass=Handler, port=port)
