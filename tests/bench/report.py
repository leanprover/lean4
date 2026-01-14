#!/usr/bin/env python3

import collections
import os
import re
import subprocess
import sys
import yaml

import temci.utils.library_init
from temci.report import stats, rundata
from temci.utils import number, settings
import scipy.stats as st

settings.Settings().load_file("cross.yaml")

def single(bench, cat, prop):
    f = f"bench/{bench}{cat}.bench"
    with open(f, "r") as f:
        runs = yaml.safe_load(f)
    stats_helper = rundata.RunDataStatsHelper.init_from_dicts(runs)
    stat = stats.TestedPairsAndSingles(stats_helper.valid_runs())
    if stat.singles:
        return stat.singles[0].properties[prop]
    else:
        raise Exception(f"failed to parse {f}")

mean_by_cat = collections.defaultdict(list)
stddev_by_cat = collections.defaultdict(list)

def pp(bench, cat, prop, norm):
    f = f"bench/{bench}{cat}.bench"
    if not open(f).read():
        return ";"
    s = single(bench, cat, prop)
    norm = norm if prop == 'etime' else 1
    mean_by_cat[cat].append(s.mean() / norm)
    stddev_by_cat[cat].append(s.std_dev() / norm)
    num = s.mean() / norm
    return f'{num:.3f};{s.std_dev() / norm:.3f}'

def mean(cat, prop):
    mean = st.gmean(mean_by_cat[cat])
    stddev = st.gmean(stddev_by_cat[cat])
    return f'{mean:.3f};{stddev:.3f}'

CATBAG = {
    '.lean': ("Lean", "etime"),
    '.no_reuse.lean': ("-reuse", "etime"),
    '.no_borrow.lean': ("-borrow", "etime"),
    '.no_st.lean': ("-ST", "etime"),
    '.gcc.lean': ("Lean+GCC9", "etime"),
    '.gc.lean': ("Lean del", "gc"),
    '.lean.perf': ("CM", "cache-misses"),
    '.hs': ("GHC", "etime"),
    '.gc.hs': ("GHC GC", "gc"),
    '.hs.perf': ("GHC CM", "cache-misses"),
    '.llvm.hs': ("GHC -fllvm", "etime"),
    '.strict.hs': ("GHC -XStrict", "etime"),
    '.ml': ("OCaml", "etime"),
    '.gc.ml': ("OCaml GC", "gc"),
    '.ml.perf': ("OCaml CM", "cache-misses"),
    '.flambda.ml': ("OCaml+Flambda", "etime"),
    '.mlton': ("MLton", "etime"),
    '.gc.mlton': ("MLton GC", "gc"),
    '.mlton.perf': ("MLton CM", "cache-misses"),
    '.mlkit': ("MLKit", "etime"),
    '.gc.mlkit': ("MLKit GC", "gc"),
    '.mlkit.perf': ("MLKit CM", "cache-misses"),
    '.swift': ("Swift", "etime"),
    '.gc.swift': ("Swift GC", "gc"),
    '.swift.perf': ("Swift CM", "cache-misses"),
}

benches = os.environ['BENCHES'].split(':')
cats = os.environ['CATS'].split(':')

# create one file without rbmap_ benchmarks, one without only rbmap and normed by rbmap_1
for sfx in ['', '_rbmap']:
    f = open(sys.argv[1] + sfx + '.csv', 'w')
    print(";".join(["Benchmark"] + [f'{CATBAG[cat][0]};{CATBAG[cat][0]} std' for cat in cats]), file=f)

    for bench in benches:
        if sfx == '' and bench.startswith('rbmap_') or sfx == '_rbmap' and not bench.startswith('rbmap'):
            continue
        norm = single('rbmap_1' if bench.startswith('rbmap') and sfx == '_rbmap' else bench, '.lean', 'etime').mean()
        print(";".join([bench] + [pp(bench, cat, CATBAG[cat][1], norm) for cat in cats]), file=f)

    print(";".join(["geom. mean"] + [mean(cat, CATBAG[cat][1]) for cat in cats]), file=f)
