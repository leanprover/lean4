#!/usr/bin/env python3

import ast
import json
import os
import sys

def read(bench, cat):
    result = json.load(open(f"bench/{bench}{cat}.bench", 'r'))[2][0]['reportAnalysis']
    mean = result['anMean']['estPoint']
    stddev = result['anStdDev']['estPoint']
    return (mean, stddev)

def pp_bench(bench, cat, norm):
    (mean, stddev) = read(bench, cat)
    return f"{mean/norm:.3f} ± {stddev/norm:.3f}"

def pp_gc_hs(bench, cat, norm):
    info = dict(ast.literal_eval(open(f"bench/{bench}{cat}.bench", 'r').read().strip()))
    gc_part = float(info['GC_cpu_seconds']) / float(info['total_cpu_seconds'])
    return f"{gc_part:.0%}"

def pp_gc_ml(bench, cat, norm):
    events = open(f"bench/{bench}{cat}.bench", 'r').readlines()
    if not events:
        return "-"
    wall_secs = float(events[-1])
    gc_nanos = 0
    for event in events[::-1]:
        data = event.split()
        # see also https://gitlab.com/gasche/gc-latency-experiment/blob/master/parse_ocaml_log.ml
        if len(data) == 4 and data[0] == '@@' and data[3] == 'dispatch':
            gc_nanos += int(data[2]) - int(data[1])
    return f"{gc_nanos*1e-9/wall_secs:.0%}"

CATBAG = {
    '.lean': ("Lean", pp_bench),
    '.gcc.lean': ("Lean+GCC9", pp_bench),
    '.hs': ("GHC", pp_bench),
    '.gc.hs': ("%GC", pp_gc_hs),
    '.llvm.hs': ("GHC -fllvm", pp_bench),
    '.llvm.gc.hs': ("%GC", pp_gc_hs),
    '.ml': ("OCaml", pp_bench),
    '.gc.ml': ("%GC", pp_gc_ml),
    '.flambda.ml': ("OCaml+Flambda", pp_bench),
}

benches = os.environ['BENCHES'].split(':')
cats = os.environ['CATS'].split(':')
print(";".join(["Benchmark"] + [CATBAG[cat][0] for cat in cats]))

for bench in benches:
    norm = read(bench, '.lean')[0]
    print(";".join([bench] + [CATBAG[cat][1](bench, cat, norm) for cat in cats]))
