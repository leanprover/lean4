"""Check the printed viewer URL serves the saved, demangled profile."""
import gzip
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time
from urllib.error import HTTPError
from urllib.parse import unquote
from urllib.request import urlopen

with tempfile.TemporaryDirectory(dir=".") as tmp, tempfile.TemporaryFile(mode="w+") as log:
    proc = subprocess.Popen(
        [sys.argv[1], "samply", "-o", "served.json.gz", "hello", *sys.argv[2:]],
        stdout=log, stderr=log, start_new_session=True,
        env={**os.environ, "TMPDIR": str(Path(tmp).resolve())},
    )
    try:
        deadline = time.monotonic() + 30
        while True:
            log.seek(0)
            output = log.read()
            match = re.search(r"https://profiler.firefox.com/from-url/(\S+)", output)
            if match:
                break
            assert proc.poll() is None, output
            assert time.monotonic() < deadline, output
            time.sleep(0.1)
        profile_url = unquote(match[1])
        assert "?" not in profile_url, profile_url
        with urlopen(profile_url, timeout=5) as response:
            assert response.headers["Content-Encoding"] == "gzip"
            data = response.read()
        assert data == Path("served.json.gz").read_bytes()
        assert json.loads(gzip.decompress(data))["meta"]["symbolicated"] is True
        try:
            urlopen(profile_url.replace("/profile.json", "/missing"), timeout=5)
        except HTTPError as error:
            assert error.code == 404
        else:
            raise AssertionError("unexpected profile at an unrelated URL")
    finally:
        os.killpg(proc.pid, signal.SIGTERM)
        proc.wait(timeout=10)
