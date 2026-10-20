#!/usr/bin/env python3
# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code

"""A mock remote artifact cache for `test.sh`.

Serves an S3-style bucket (`GET`/`PUT` of `<store>/<path>`) and the part of the
Reservoir API that Lake uses. Faults are selected by the first path segment, so
a test picks one by pointing an endpoint at it (e.g. `.../corrupt/a0`):

  ok        serve and store normally
  deny      403 with an S3-style XML error body
  corrupt   200 with the right length but mutated bytes
  truncate  200 with a full `Content-Length` but half a body, then disconnect
  reset     disconnect without a response (curl writes no output file)
  empty     200 and a `Content-Length` but no body, for an object that is not
            in the store, so that curl leaves no output file to read
  badcount  Reservoir artifact URL lookup returns too few URLs
  apierror  Reservoir requests return an API error object

A fault that does not apply to a request kind (e.g. `badcount` on a `GET`)
behaves as `ok`. Each request is logged to stdout as `<method> <path> -> <status>`.

This is Python rather than `Std.Http` because `truncate` and `reset` are
transport-level faults: a body cut short of its declared `Content-Length` and a
closed connection with no response at all. A conforming response writer cannot
emit either, so a Lean server would have to hand-roll HTTP/1.1 over `Std.Net.TCP`.
Revisit if `Std.Http` gains a way to abort a response mid-body.
"""

import argparse
import json
import os
import sys
from enum import StrEnum
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlparse

ARTIFACT_TYPE = "application/vnd.reservoir.artifact"
MAP_TYPE = "application/vnd.reservoir.outputs+json-lines"

DENY_BODY = (
    b'<?xml version="1.0" encoding="UTF-8"?>\n'
    b"<Error><Code>AccessDenied</Code><Message>mock denial</Message></Error>\n"
)

STORE = "."


class Mode(StrEnum):
    """A fault mode, named by the first segment of a request path."""

    OK = "ok"
    DENY = "deny"
    CORRUPT = "corrupt"
    TRUNCATE = "truncate"
    RESET = "reset"
    EMPTY = "empty"
    BAD_COUNT = "badcount"
    API_ERROR = "apierror"


def content_type(path):
    if path.endswith(".art"):
        return ARTIFACT_TYPE
    elif path.endswith(".jsonl"):
        return MAP_TYPE
    else:
        return "application/octet-stream"


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    # Requests are logged by the handlers below, which also know about the
    # faults that never send a response.
    def log_request(self, code="-", size="-"):
        pass

    def log_message(self, format, *args):
        pass

    def log(self, status):
        print("%s %s -> %s" % (self.command, self.path, status), flush=True)

    def parse(self):
        """Split a path into its fault mode and the object path under it.

        Returns no mode for a path that names no fault mode, which is a
        misconfigured endpoint rather than a cache miss.
        """
        url = urlparse(self.path)
        parts = [unquote(p) for p in url.path.split("/") if p]
        if any(p in (os.curdir, os.pardir) or os.path.isabs(p) for p in parts):
            return None, [], {}
        try:
            mode = Mode(parts[0]) if parts else None
        except ValueError:
            mode = None
        if mode is None:
            return None, [], {}
        return mode, parts[1:], parse_qs(url.query)

    def respond(self, status, body, ctype):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
        self.log(status)

    def not_found(self, message):
        body = json.dumps({"error": {"status": 404, "message": message}})
        self.respond(404, body.encode(), "application/json")

    def deny(self):
        self.respond(403, DENY_BODY, "application/xml")

    def reset(self):
        # Neither a response nor a body: `curl` reports an empty reply and,
        # importantly, does not create its output file.
        self.close_connection = True
        self.log("reset")

    def serve(self, mode, path, ctype=None):
        try:
            with open(path, "rb") as f:
                data = f.read()
        except FileNotFoundError:
            if mode == Mode.EMPTY:
                # Announcing a body that never arrives: curl reports HTTP 200
                # yet never creates its output file
                self.send_response(200)
                self.send_header("Content-Type", ctype or content_type(path))
                self.send_header("Content-Length", "100")
                self.end_headers()
                self.close_connection = True
                self.log("no body")
            else:
                self.not_found("no such object: %s" % self.path)
            return
        ctype = ctype or content_type(path)
        if mode == Mode.CORRUPT:
            data = data[:-1] + bytes([data[-1] ^ 0xFF]) if data else b"corrupt"
            self.respond(200, data, ctype)
        elif mode == Mode.TRUNCATE:
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data[: len(data) // 2])
            self.close_connection = True
            self.log("truncated")
        else:
            self.respond(200, data, ctype)

    def find_revision(self, scope, rev):
        """Locate a revision's outputs, ignoring any platform/toolchain path."""
        root = os.path.join(STORE, "r0", *scope)
        for dir, _, files in os.walk(root):
            if rev + ".jsonl" in files:
                return os.path.join(dir, rev + ".jsonl")
        return None

    def reservoir_get(self, mode, parts, query):
        # `parts` is `<packages|repositories>/<owner>/<name>/<endpoint>`
        scope, endpoint = parts[1:3], parts[3:]
        if endpoint[:1] == ["build-outputs"]:
            rev = query.get("rev", [""])[0]
            path = self.find_revision(scope, rev)
            if path is None:
                self.not_found("no outputs for revision %s" % rev)
            else:
                self.serve(mode, path)
        elif endpoint[:1] == ["artifacts"] and len(endpoint) == 2:
            self.serve(mode, os.path.join(STORE, "a0", *(scope + endpoint[1:])))
        else:
            self.not_found("no such endpoint: %s" % self.path)

    def reservoir_post(self, mode, parts):
        # Lake fetches the storage URLs of a batch of artifacts in one request
        scope, endpoint = parts[1:3], parts[3:]
        if endpoint != ["artifacts"]:
            self.not_found("no such endpoint: %s" % self.path)
            return
        length = int(self.headers.get("Content-Length", 0))
        hashes = json.loads(self.rfile.read(length).decode())
        if mode == Mode.API_ERROR:
            body = {"error": {"status": 503, "message": "mock API error"}}
        else:
            host = self.headers.get("Host")
            urls = [
                "http://%s/%s/a0/%s/%s.art" % (host, mode, "/".join(scope), hash)
                for hash in hashes
            ]
            if mode == Mode.BAD_COUNT:
                urls = urls[:-1]
            body = {"data": urls}
        self.respond(200, json.dumps(body).encode(), "application/json")

    def do_GET(self):
        mode, parts, query = self.parse()
        if mode is None:
            self.not_found("no fault mode in path: %s" % self.path)
        elif mode == Mode.RESET:
            self.reset()
        elif mode == Mode.DENY:
            self.deny()
        elif parts[:2] == ["api", "v1"]:
            self.reservoir_get(mode, parts[2:], query)
        else:
            self.serve(mode, os.path.join(STORE, *parts))

    def do_POST(self):
        mode, parts, _ = self.parse()
        if mode is None:
            self.not_found("no fault mode in path: %s" % self.path)
        elif mode == Mode.RESET:
            self.reset()
        elif mode == Mode.DENY:
            self.deny()
        elif parts[:2] == ["api", "v1"]:
            self.reservoir_post(mode, parts[2:])
        else:
            self.not_found("no such endpoint: %s" % self.path)

    def do_PUT(self):
        mode, parts, _ = self.parse()
        # The body is always consumed so that `curl` sees a complete exchange
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length)
        if mode is None:
            self.not_found("no fault mode in path: %s" % self.path)
        elif mode == Mode.RESET:
            self.reset()
        elif mode == Mode.DENY:
            self.deny()
        else:
            path = os.path.join(STORE, *parts)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "wb") as f:
                f.write(body)
            self.respond(200, b"", "application/xml")


class Server(ThreadingHTTPServer):
    daemon_threads = True

    # Lake aborts transfers on error, which is not a server failure
    def handle_error(self, request, client_address):
        if not isinstance(sys.exception(), ConnectionError):
            super().handle_error(request, client_address)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--store", required=True, help="directory to serve")
    parser.add_argument(
        "--port-file", required=True, help="where to write the bound port"
    )
    parser.add_argument("--host", default="127.0.0.1")
    args = parser.parse_args()

    global STORE
    STORE = args.store
    os.makedirs(STORE, exist_ok=True)

    # Port 0 lets the OS pick a free port, so parallel tests cannot collide
    server = Server((args.host, 0), Handler)
    port = server.server_address[1]
    # Written atomically so that a test can wait on the file to know the
    # server is accepting connections
    with open(args.port_file + ".tmp", "w") as f:
        f.write("%s\n" % port)
    os.replace(args.port_file + ".tmp", args.port_file)
    print("serving %s on %s:%s" % (STORE, args.host, port), flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
