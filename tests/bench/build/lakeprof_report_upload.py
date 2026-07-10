#!/usr/bin/env python3

import json
import os
import subprocess
import sys
from pathlib import Path

upload_url = os.environ.get("LAKEPROF_UPLOAD_URL")
if not upload_url:
    sys.exit(0)
if upload_url.endswith("/"):
    upload_url = upload_url[:-1]

# Determine paths relative to the current file.
script_file = Path(__file__)
template_file = script_file.parent / "lakeprof_report_template.html"
src_dir = script_file.parent.parent.parent.parent / "src"


def run_stdout(*command: str, cwd: Path | None = None) -> str:
    result = subprocess.run(command, capture_output=True, encoding="utf-8", cwd=cwd)
    if result.returncode != 0:
        print(result.stdout, end="", file=sys.stdout)
        print(result.stderr, end="", file=sys.stderr)
        sys.exit(result.returncode)
    return result.stdout


sha = run_stdout("git", "rev-parse", "@", cwd=src_dir).strip()
base_url = f"{upload_url}/{sha}"
report = (src_dir / "lakeprof_report.txt").read_text()

template = template_file.read_text()
template = template.replace("__BASE_URL__", json.dumps(base_url))
template = template.replace("__LAKEPROF_REPORT__", report)
(src_dir / "index.html").write_text(template)


def upload(file: Path) -> None:
    subprocess.run(["curl", "-fT", file, f"{base_url}/{file.name}"], check=True)


upload(src_dir / "index.html")
upload(src_dir / "lakeprof.log")
upload(src_dir / "lakeprof.trace_event")
