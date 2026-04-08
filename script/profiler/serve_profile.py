#!/usr/bin/env python3
"""
Serve a Firefox Profiler JSON file and open it in the browser.

Unlike `samply load`, this does NOT provide a symbolication API,
so Firefox Profiler will use the names already in the profile as-is.
"""

import argparse
import gzip
import http.server
import io
import sys
import threading
import webbrowser
import urllib.parse


class ProfileHandler(http.server.BaseHTTPRequestHandler):
    """Serve the profile JSON and handle CORS for Firefox Profiler."""

    profile_data = None  # set by main()

    def do_GET(self):
        if self.path == "/profile.json":
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Encoding", "gzip")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()
            self.wfile.write(self.profile_data)
        else:
            self.send_response(404)
            self.end_headers()

    def do_OPTIONS(self):
        # CORS preflight
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def log_message(self, format, *args):
        pass  # suppress request logs


def main():
    parser = argparse.ArgumentParser(
        description="Serve a profile JSON for Firefox Profiler")
    parser.add_argument("profile", help="Profile file (.json or .json.gz)")
    parser.add_argument("-P", "--port", type=int, default=3457,
                        help="Port to serve on (default: 3457)")
    parser.add_argument("-n", "--no-open", action="store_true",
                        help="Do not open the browser")
    args = parser.parse_args()

    # Read the profile data (keep it gzipped for efficient serving)
    if args.profile.endswith(".gz"):
        with open(args.profile, "rb") as f:
            ProfileHandler.profile_data = f.read()
    else:
        with open(args.profile, "rb") as f:
            raw = f.read()
        buf = io.BytesIO()
        with gzip.GzipFile(fileobj=buf, mode="wb") as gz:
            gz.write(raw)
        ProfileHandler.profile_data = buf.getvalue()

    http.server.HTTPServer.allow_reuse_address = True
    server = http.server.HTTPServer(("127.0.0.1", args.port), ProfileHandler)
    profile_url = f"http://127.0.0.1:{args.port}/profile.json"
    encoded = urllib.parse.quote(profile_url, safe="")
    viewer_url = f"https://profiler.firefox.com/from-url/{encoded}"

    if not args.no_open:
        # Open browser after a short delay to let server start
        def open_browser():
            webbrowser.open(viewer_url)
        threading.Timer(0.5, open_browser).start()

    print(f"Serving profile at {profile_url}", file=sys.stderr)
    print(f"Firefox Profiler: {viewer_url}", file=sys.stderr)
    print("Press Ctrl+C to stop.", file=sys.stderr)

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.", file=sys.stderr)
        server.server_close()


if __name__ == "__main__":
    main()
