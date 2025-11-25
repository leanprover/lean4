#!/usr/bin/env python3

import json
import subprocess
import sys
from pathlib import Path


def run(*args: str) -> None:
    subprocess.run(args, check=True)


def run_stdout(*command: str, cwd: str | None = None) -> str:
    result = subprocess.run(command, capture_output=True, encoding="utf-8", cwd=cwd)
    if result.returncode != 0:
        print(result.stdout, end="", file=sys.stdout)
        print(result.stderr, end="", file=sys.stderr)
        sys.exit(result.returncode)
    return result.stdout


def main() -> None:
    script_file = Path(__file__)
    template_file = script_file.parent / "lakeprof_report_template.html"

    sha = run_stdout("git", "rev-parse", "@").strip()
    base_url = f"https://speed.lean-lang.org/lean4-out/{sha}"
    report = run_stdout("lakeprof", "report", "-prc", cwd="src")
    with open(template_file) as f:
        template = f.read()

    template = template.replace("__BASE_URL__", json.dumps(base_url))
    template = template.replace("__LAKEPROF_REPORT__", report)

    with open("index.html", "w") as f:
        f.write(template)

    run("curl", "-T", "index.html", f"{base_url}/index.html")
    run("curl", "-T", "src/lakeprof.log", f"{base_url}/lakeprof.log")
    run("curl", "-T", "src/lakeprof.trace_event", f"{base_url}/lakeprof.trace_event")


if __name__ == "__main__":
    main()
