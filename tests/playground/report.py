#!/usr/bin/env python3

import os
import re
import subprocess
import sys
import yaml

import temci.utils.library_init
from temci.report import stats, rundata
from temci.utils import number, settings

def pp(bench, cat, prop):
    f = f"bench/{bench}{cat}.bench"
    if not open(f).read():
        return "-"
    with open(f, "r") as f:
        runs = yaml.load(f)
    stats_helper = rundata.RunDataStatsHelper.init_from_dicts(runs)
    stat = stats.TestedPairsAndSingles(stats_helper.valid_runs())
    n = stat.singles[0].properties[prop]
    return number.fnumber(n.mean(), abs_deviation=n.std_dev())

CATBAG = {
    '.lean': ("Lean [s]", "etime"),
    '.gcc.lean': ("Lean+GCC9", "etime"),
    '.gc.lean': ("del [%]", "gc"),
    '.lean.perf': ("cache misses [1M/s]", "cache-misses"),
    '.hs': ("GHC", "etime"),
    '.gc.hs': ("GC [%]", "gc"),
    '.hs.perf': ("cache misses", "cache-misses"),
    '.llvm.hs': ("GHC -fllvm", "etime"),
    '.ml': ("OCaml", "etime"),
    '.gc.ml': ("%GC", "gc"),
    '.ml.perf': ("cache misses", "cache-misses"),
    '.flambda.ml': ("OCaml+Flambda", "etime"),
    '.mlton': ("MLton", "etime"),
    '.gc.mlton': ("%GC", "gc"),
    '.mlton.perf': ("cache misses", "cache-misses"),
    '.mlkit': ("MLKit", "etime"),
    '.gc.mlkit': ("%GC", "gc"),
    '.mlkit.perf': ("cache misses", "cache-misses"),
}

benches = os.environ['BENCHES'].split(':')
cats = os.environ['CATS'].split(':')
print(";".join(["Benchmark"] + [CATBAG[cat][0] for cat in cats]))

for bench in benches:
    print(";".join([bench] + [pp(bench, cat, CATBAG[cat][1]) for cat in cats]))
