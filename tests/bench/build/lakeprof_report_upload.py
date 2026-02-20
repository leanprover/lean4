#!/usr/bin/env python3

import json
import subprocess
import sys
from pathlib import Path

# Determine paths relative to the current file.
script_file = Path(__file__)
src_dir = script_file.parent.parent.parent.parent / "src"
template_file = script_file.parent / "lakeprof_report_template.html"


def run_stdout(*command: str, cwd: Path | None = None) -> str:
    result = subprocess.run(command, capture_output=True, encoding="utf-8", cwd=cwd)
    if result.returncode != 0:
        print(result.stdout, end="", file=sys.stdout)
        print(result.stderr, end="", file=sys.stderr)
        sys.exit(result.returncode)
    return result.stdout


sha = run_stdout("git", "rev-parse", "@", cwd=src_dir).strip()
base_url = f"https://speed.lean-lang.org/lean4-out/{sha}"
report = run_stdout("lakeprof", "report", "-prc", cwd=src_dir)

template = template_file.read_text()
template = template.replace("__BASE_URL__", json.dumps(base_url))
template = template.replace("__LAKEPROF_REPORT__", report)
(src_dir / "index.html").write_text(template)


def upload(file: Path) -> None:
    subprocess.run(["curl", "-fT", file, f"{base_url}/{file.name}"], check=True)


upload(src_dir / "index.html")
upload(src_dir / "lakeprof.log")
upload(src_dir / "lakeprof.trace_event")
