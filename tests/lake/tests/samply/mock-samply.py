#!/usr/bin/env python3
"""Deterministic samply substitute: exercise Lake without perf permissions."""
import gzip
import json
import os
from pathlib import Path
import sys
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import quote

COUNT = 20000  # The symbolication request exceeds Linux's per-argument size limit.


def profile():
    return {
        "meta": {"symbolicated": False},
        "libs": [{"debugName": "hello", "breakpadId": "ABC"}],
        "threads": [{
            "frameTable": {
                "func": [0, 0, *range(1, COUNT), COUNT],
                "address": [-1, *range(COUNT), -1],
                "length": COUNT + 2,
            },
            "funcTable": {"name": [0] * (COUNT + 1), "resource": [0] * COUNT + [-1]},
            "resourceTable": {"lib": [0]},
            "stringArray": ["shared label"],
        }, {
            "frameTable": {"func": [0], "address": [7], "length": 1},
            "funcTable": {"name": [0], "resource": [0]},
            "resourceTable": {"lib": [0]},
            "stringArray": ["other thread"],
        }],
    }


args = sys.argv[1:]
if args[0] == "record":
    assert args[1:3] == ["--save-only", "-o"], args
    sep = args.index("--")
    assert args[4:sep] == ["--rate", "123"], args
    assert args[sep + 2:] == ["an argument with spaces", "--flag"], args
    lean_path = [Path(p).resolve() for p in os.environ.get("LEAN_PATH", "").split(os.pathsep)]
    assert Path(".lake/build/lib/lean").resolve() in lean_path, lean_path
    if os.environ.get("SAMPLY_TEST_FAIL"):
        print("deliberate recording failure", file=sys.stderr)
        sys.exit(17)
    with gzip.open(args[3], "wt") as out:
        json.dump(profile(), out)
elif args[0] == "load":
    profile_path = Path(args[-1])
    port = int(args[args.index("-P") + 1])

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_POST(self):
            assert self.path == "/testtoken/symbolicate/v5", self.path
            if os.environ.get("SAMPLY_TEST_RESPONSE") == "http-error":
                self.send_error(500)
                return
            request = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
            assert request["memoryMap"] == [["hello", "ABC"]]
            frames = [frame for stack in request["stacks"] for frame in stack]
            assert frames == [[0, i] for i in range(COUNT)] + [[0, 7]], frames[:10]
            stacks = [[{"function": f"l_Test_f{addr}"} if addr % 2 == 0
                       else f"l_Test_f{addr}" for _, addr in stack]
                      for stack in request["stacks"]]
            if os.environ.get("SAMPLY_TEST_RESPONSE") == "short":
                stacks[0].pop()
            body = json.dumps({"results": [{"stacks": stacks}]}).encode()
            self.send_response(200)
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            if self.path != "/testtoken/profile.json":
                self.send_error(404)
                return
            self.send_response(200)
            self.send_header("Content-Encoding", "gzip")
            self.end_headers()
            self.wfile.write(profile_path.read_bytes())

    with HTTPServer(("127.0.0.1", port), Handler) as server:
        print("https://profiler.firefox.com/from-url/" +
              quote(f"http://127.0.0.1:{port}/testtoken/profile.json", safe=""),
              file=sys.stderr, flush=True)
        server.serve_forever()
else:
    raise AssertionError(args)
