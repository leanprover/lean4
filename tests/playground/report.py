#!/usr/bin/env python3

import os
import re
import subprocess
import sys
import yaml

from temci.utils import util
util.allow_all_imports = True
import temci.scripts.cli  # side effects may include: registering settings, loading settings object, ...
from temci.report import stats, rundata
from temci.utils import number, settings

number.FNumber.init_settings(settings.Settings()["report/number"])

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
    '.gc.lean': ("GC [%]", "gc"),
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
