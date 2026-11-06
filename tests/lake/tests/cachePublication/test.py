"""Exercise atomic publication through ordinary native cache APIs."""

import http.server
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest


class Publication(unittest.TestCase):
    def paused_copy(self, command, root, final_pattern, *, copy_source=None, killed=False):
        pause = root / "pause"
        pause.mkdir()
        library = root / "pause.so"
        result = subprocess.run(["cc", "-shared", "-fPIC", "-o", str(library),
                                 "pause_write.c", "-ldl"], capture_output=True, text=True,
                                env={k: v for k, v in os.environ.items() if k != "LD_LIBRARY_PATH"})
        self.assertEqual(result.returncode, 0, result.stderr)
        artifacts = root / "cache/artifacts"
        env = dict(os.environ, LD_PRELOAD=str(library), TEST_WRITE_PREFIX=str(artifacts),
                   TEST_WRITE_PAUSE_DIR=str(pause))
        if copy_source is not None:
            env["TEST_COPY_SOURCE"] = str(copy_source)
        child = subprocess.Popen(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 60
            while not (pause / "paused").exists() and child.poll() is None and time.monotonic() < deadline:
                time.sleep(0.01)
            self.assertTrue((pause / "paused").exists(), "copy did not enter the controlled partial-write window")
            partial = pathlib.Path((pause / "paused").read_text())
            self.assertEqual(partial.stat().st_size, 4096)
            self.assertEqual(list(artifacts.glob(final_pattern)), [], "reader can see partial artifact bytes")
            if killed:
                child.kill()
        finally:
            (pause / "release").touch()
            try:
                out, err = child.communicate(timeout=60)
            except subprocess.TimeoutExpired:
                child.kill()
                child.communicate(timeout=60)
                raise
        if killed:
            self.assertNotEqual(child.returncode, 0)
            self.assertEqual(list(artifacts.glob(final_pattern)), [])
        else:
            self.assertEqual(child.returncode, 0, out + err)
            self.assertEqual(next(artifacts.glob(final_pattern)).read_bytes(), b"x" * 8192)

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "write interposition needs Linux and cc")
    def test_slow_local_artifact_copies_publish_only_complete_bytes(self):
        for mode in ("save", "save-text"):
            for killed in (False, True):
                with self.subTest(mode=mode, killed=killed), tempfile.TemporaryDirectory() as tmp:
                    root = pathlib.Path(tmp)
                    source = root / "source"
                    source.write_bytes(b"x" * 8192)
                    self.paused_copy([os.environ.get("LEAN", "lean"), "--run", "Probe.lean", mode,
                                      str(root / "cache"), str(source)], root, "*.art",
                                     copy_source=source, killed=killed)

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "write interposition needs Linux and cc")
    def test_extra_download_destinations_publish_only_complete_bytes(self):
        body = b"x" * 8192
        arrivals = []
        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self):
                arrivals.append(1)
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            def log_message(self, *_):
                pass
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            for warm in (False, True):
                with self.subTest(warm=warm), tempfile.TemporaryDirectory() as tmp:
                    root = pathlib.Path(tmp)
                    command = [os.environ.get("LEAN", "lean"), "--run", "Probe.lean", "batch",
                               f"http://127.0.0.1:{server.server_port}/artifact", str(root / "cache"), body.decode()]
                    if warm:
                        result = subprocess.run(command, capture_output=True, text=True)
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    before = len(arrivals)
                    command[3] = "batch-extra"
                    self.paused_copy(command, root, "*.extra")
                    self.assertEqual(len(arrivals) - before, 0 if warm else 1)
                    self.assertEqual(next((root / "cache/artifacts").glob("*.art")).read_bytes(), body)
        finally:
            server.shutdown()
            server.server_close()
            thread.join()

    @unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("cc"), "link interposition needs Linux and cc")
    def test_publication_on_filesystem_rejecting_hard_links(self):
        for mode in ("save", "save-text"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as tmp:
                root = pathlib.Path(tmp)
                library = root / "deny-link.so"
                subprocess.run(["cc", "-shared", "-fPIC", "-o", str(library),
                                "pause_write.c", "-ldl"], check=True,
                               env={k: v for k, v in os.environ.items() if k != "LD_LIBRARY_PATH"})
                source = root / "source"
                source.write_bytes(b"complete artifact bytes\n")
                cache = root / "cache"
                env = dict(os.environ, LD_PRELOAD=str(library), TEST_LINK_DENIED_PREFIX=str(cache))
                result = subprocess.run([os.environ.get("LEAN", "lean"), "--run", "Probe.lean",
                                         mode, str(cache), str(source)], env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                target, = (cache / "artifacts").glob("*.art")
                self.assertEqual(target.read_bytes(), source.read_bytes())
                self.assertEqual(target.stat().st_mode & 0o222, 0)
                self.assertEqual(list(cache.rglob(".lake-cache-*.tmp")), [])

    def paused_download(self, mode):
        body = b"a complete native artifact"
        started = threading.Event()
        release = threading.Event()

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self):
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body[:4])
                self.wfile.flush()
                started.set()
                release.wait(60)
                self.wfile.write(body[4:])

            def log_message(self, *_):
                pass

        with tempfile.TemporaryDirectory() as tmp:
            target = pathlib.Path(tmp) / "artifact.art"
            server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            command = [os.environ.get("LEAN", "lean"), "--run", "Probe.lean", mode,
                       f"http://127.0.0.1:{server.server_port}/artifact",
                       str(target if mode == "fetch" else pathlib.Path(tmp)), body.decode()]
            child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                for _ in range(600):
                    if started.wait(0.1):
                        break
                    if child.poll() is not None:
                        out, err = child.communicate()
                        self.fail("native downloader exited before reaching the server: " + out + err)
                self.assertTrue(started.is_set(), "native downloader never reached the local server")
                if mode == "fetch":
                    self.assertFalse(target.exists(), "native reader can see partial bytes under the final name")
                else:
                    self.assertEqual(list((pathlib.Path(tmp) / "artifacts").glob("*.art")), [])
            finally:
                release.set()
                out, err = child.communicate(timeout=60)
                server.shutdown()
                server.server_close()
                thread.join()
            self.assertEqual(child.returncode, 0, out + err)
            if mode == "batch":
                target = next((pathlib.Path(tmp) / "artifacts").glob("*.art"))
            self.assertEqual(target.read_bytes(), body)

    def test_lazy_fetch_never_exposes_partial_artifact(self):
        self.paused_download("fetch")

    def test_batch_fetch_never_exposes_partial_artifact(self):
        self.paused_download("batch")

    def test_overlapping_downloads_survive_a_killed_publisher(self):
        for mode, killed in (("fetch", False), ("fetch", True), ("batch", False), ("batch", True)):
            with self.subTest(mode=mode, killed=killed), tempfile.TemporaryDirectory() as tmp:
                target = pathlib.Path(tmp) / "artifact.art"
                body = b"a complete artifact from the surviving publisher"
                release = threading.Event()
                both_started = threading.Event()
                arrivals = []
                class Handler(http.server.BaseHTTPRequestHandler):
                    def do_GET(self):
                        self.send_response(200)
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body[:4])
                        self.wfile.flush()
                        arrivals.append(1)
                        if len(arrivals) == 2:
                            both_started.set()
                        release.wait(60)
                        try:
                            self.wfile.write(body[4:])
                        except BrokenPipeError:
                            pass
                    def log_message(self, *_):
                        pass
                server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
                thread = threading.Thread(target=server.serve_forever, daemon=True)
                thread.start()
                command = [os.environ.get("LEAN", "lean"), "--run", "Probe.lean", mode,
                           f"http://127.0.0.1:{server.server_port}/artifact",
                           str(target if mode == "fetch" else pathlib.Path(tmp)), body.decode()]
                children = [subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                            for _ in range(2)]
                try:
                    self.assertTrue(both_started.wait(60), "both native writers must reach the server")
                    self.assertFalse(target.exists())
                    if killed:
                        children[0].kill()
                        children[0].communicate(timeout=60)
                    release.set()
                    for child in children[1:] if killed else children:
                        out, err = child.communicate(timeout=60)
                        self.assertEqual(child.returncode, 0, out + err)
                    if mode == "batch":
                        target = next((pathlib.Path(tmp) / "artifacts").glob("*.art"))
                    self.assertEqual(target.read_bytes(), body)
                finally:
                    release.set()
                    for child in children:
                        if child.poll() is None:
                            child.kill()
                        child.communicate(timeout=60)
                    server.shutdown()
                    server.server_close()
                    thread.join()

    def test_concurrent_metadata_publication_exposes_only_whole_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            children = [subprocess.Popen([os.environ.get("LEAN", "lean"), "--run", "Probe.lean",
                                          "metadata", tmp, value], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                         text=True) for value in ("a", "b")]
            reads = 0
            try:
                deadline = time.monotonic() + 60
                while any(child.poll() is None for child in children) and time.monotonic() < deadline:
                    for path in root.glob("outputs/fixture/*.json"):
                        data = json.loads(path.read_text())["data"]
                        self.assertTrue(data == "a" * 65536 or data == "b" * 65536)
                        reads += 1
                    time.sleep(0.001)
                for child in children:
                    out, err = child.communicate(timeout=60)
                    self.assertEqual(child.returncode, 0, out + err)
                self.assertGreater(reads, 0)
            finally:
                for child in children:
                    if child.poll() is None:
                        child.kill()
                    child.communicate(timeout=60)


if __name__ == "__main__":
    unittest.main()
