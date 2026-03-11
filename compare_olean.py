#!/usr/bin/env python3
import os

stage1_dir = "build/release/stage1"
stage2_dir = "build/release/stage2"

def collect_olean_private(base):
    result = {}
    for root, _, files in os.walk(base):
        for f in files:
            if f.endswith(".c"):
                full = os.path.join(root, f)
                rel = os.path.relpath(full, base)
                f = open(full, "r")
                size = len(f.readlines())
                result[rel] = size
    return result

s1 = collect_olean_private(stage1_dir)
s2 = collect_olean_private(stage2_dir)

common = s1.keys() & s2.keys()
diffs = []
for rel in common:
    d = s2[rel] - s1[rel]
    if d != 0:
        diffs.append((rel, s1[rel], s2[rel], d))

diffs.sort(key=lambda x: x[3])

for rel, sz1, sz2, d in diffs:
    print(f"{d:+10d}  {sz1:>10d} -> {sz2:>10d}  {rel}")

total1 = sum(s1[r] for r, _, _, _ in diffs)
total2 = sum(s2[r] for r, _, _, _ in diffs)
print(f"\n{'Total:':>10s}  {total1:>10d} -> {total2:>10d}  ({total2 - total1:+d})")
