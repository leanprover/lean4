#!/usr/bin/env python3
"""
Lean name demangler — thin wrapper around the Lean CLI tool.

Spawns ``lean --run lean_demangle_cli.lean`` as a persistent subprocess
and communicates via stdin/stdout pipes. This ensures a single source
of truth for demangling logic (the Lean implementation in
``Lean.Compiler.NameDemangling``).

Usage as a filter (like c++filt):
    echo "l_Lean_Meta_Sym_main" | python lean_demangle.py

Usage as a module:
    from lean_demangle import demangle_lean_name
    print(demangle_lean_name("l_Lean_Meta_Sym_main"))
"""

import atexit
import os
import subprocess
import sys

_process = None
_script_dir = os.path.dirname(os.path.abspath(__file__))
_cli_script = os.path.join(_script_dir, "lean_demangle_cli.lean")


def _get_process():
    """Get or create the persistent Lean demangler subprocess."""
    global _process
    if _process is not None and _process.poll() is None:
        return _process

    lean = os.environ.get("LEAN", "lean")
    _process = subprocess.Popen(
        [lean, "--run", _cli_script],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        bufsize=1,  # line buffered
    )
    atexit.register(_cleanup)
    return _process


def _cleanup():
    global _process
    if _process is not None:
        try:
            _process.stdin.close()
            _process.wait(timeout=5)
        except Exception:
            _process.kill()
        _process = None


def demangle_lean_name(mangled):
    """
    Demangle a C symbol name produced by the Lean 4 compiler.

    Returns a human-friendly demangled name, or the original string
    if it is not a Lean symbol.
    """
    try:
        proc = _get_process()
        proc.stdin.write(mangled + "\n")
        proc.stdin.flush()
        result = proc.stdout.readline().rstrip("\n")
        return result if result else mangled
    except Exception:
        return mangled


def main():
    """Filter stdin, demangling Lean names."""
    for line in sys.stdin:
        print(demangle_lean_name(line.rstrip("\n")))


if __name__ == "__main__":
    main()
