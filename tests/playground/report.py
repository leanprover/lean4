#!/usr/bin/env python3

import os
import re
import subprocess
import sys

def pp(bench, cat, prop):
    f = f"bench/{bench}{cat}.bench"
    if not open(f).read():
        return "-"
    p = subprocess.run([os.environ['TEMCI'], "report", f, "--reporter", "csv", "--csv_columns", f"{prop}[mean|o]"], stdout=subprocess.PIPE)
    return p.stdout.decode('utf8').splitlines()[1]

CATBAG = {
    '.lean': ("Lean [s]", "etime"),
    '.gcc.lean': ("Lean+GCC9", "etime"),
    '.lean.perf': ("cache misses [1M/s]", "cache-misses"),
    '.hs': ("GHC", "etime"),
    '.gc.hs': ("GC [%]", "gc"),
    '.hs.perf': ("cache misses", "cache-misses"),
    '.llvm.hs': ("GHC -fllvm", "etime"),
    '.ml': ("OCaml", "etime"),
    '.gc.ml': ("%GC", "gc"),
    '.ml.perf': ("cache misses", "cache-misses"),
    '.flambda.ml': ("OCaml+Flambda", "etime"),
}

benches = os.environ['BENCHES'].split(':')
cats = os.environ['CATS'].split(':')
print(";".join(["Benchmark"] + [CATBAG[cat][0] for cat in cats]))

for bench in benches:
    print(";".join([bench] + [pp(bench, cat, CATBAG[cat][1]) for cat in cats]))
