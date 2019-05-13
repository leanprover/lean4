#!/usr/bin/env python3

import json
import os
import sys

CATBAG = {
    '.lean': "Lean",
    '.gcc.lean': "Lean+GCC9",
    '.hs': "GHC",
    '.llvm.hs': "GHC -fllvm",
    '.ml': "OCaml",
    '.flambda.ml': "OCaml+Flambda"
}

benches = os.environ['BENCHES'].split(':')
cats = os.environ['CATS'].split(':')
print(";".join(["Benchmark"] + [CATBAG[cat] for cat in cats]))

def read(bench, cat):
    result = json.load(open(f"bench/{bench}{cat}.bench", 'r'))[2][0]['reportAnalysis']
    mean = result['anMean']['estPoint']
    stddev = result['anStdDev']['estPoint']
    return (mean, stddev)

def pp(bench, cat, norm):
    (mean, stddev) = read(bench, cat)
    return f"{mean/norm:.3} ± {stddev/norm:.3}"

for bench in benches:
    norm = read(bench, '.lean')[0]
    print(";".join([bench] + [pp(bench, cat, norm) for cat in cats]))
