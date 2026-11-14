"""An on-demand download becomes visible only after completion and validation."""

import http.server
import os
import pathlib
import subprocess
import tempfile
import threading
import unittest


class Download(unittest.TestCase):
    def test_successful_download(self):
        self.download("success")

    def test_hash_mismatch(self):
        self.download("corrupt")

    def test_interrupted_transfer(self):
        self.download("incomplete")

    def download(self, outcome):
        expected = b"complete artifact bytes"
        payload = b"incorrect artifact bytes" if outcome == "corrupt" else expected
        for existing in (False, True):
            with self.subTest(existing=existing), tempfile.TemporaryDirectory() as temporary:
                path = pathlib.Path(temporary) / "artifacts/artifact.art"
                previous = b"previous artifact bytes"
                if existing:
                    path.parent.mkdir()
                    path.write_bytes(previous)
                started, release = threading.Event(), threading.Event()

                class Handler(http.server.BaseHTTPRequestHandler):
                    def do_GET(self):
                        self.send_response(200)
                        self.send_header("Content-Length", str(len(payload)))
                        self.end_headers()
                        self.wfile.write(payload[:4])
                        self.wfile.flush()
                        started.set()
                        release.wait(30)
                        if outcome != "incomplete":
                            self.wfile.write(payload[4:])

                    def log_message(self, *_):
                        pass

                server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
                server.daemon_threads = True
                thread = threading.Thread(target=server.serve_forever, daemon=True)
                thread.start()
                child = subprocess.Popen(
                    [os.environ.get("LEAN", "lean"), "-Dinterpreter.prefer_native=false", "--run", "Probe.lean",
                     f"http://127.0.0.1:{server.server_port}/artifact", str(path), expected.decode()],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                )
                try:
                    self.assertTrue(started.wait(30), "native downloader did not reach the server")
                    if existing:
                        self.assertEqual(path.read_bytes(), previous, "download changed the final name before completion")
                    else:
                        self.assertFalse(path.exists(), "partial download is visible under the final name")
                finally:
                    release.set()
                    try:
                        out, err = child.communicate(timeout=30)
                    except subprocess.TimeoutExpired:
                        child.kill()
                        child.communicate()
                        raise
                    finally:
                        server.shutdown()
                        server.server_close()
                        thread.join()
                self.assertEqual(child.returncode == 0, outcome == "success", out + err)
                if outcome == "success":
                    self.assertEqual(path.read_bytes(), expected)
                elif existing:
                    self.assertEqual(path.read_bytes(), previous)
                else:
                    self.assertFalse(path.exists())
                self.assertEqual(list(path.parent.iterdir()), [path] if path.exists() else [], "staging was not removed")


if __name__ == "__main__":
    unittest.main()
