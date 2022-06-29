#!/usr/bin/env python3

import sys

[misses, wall_secs] = sys.stdin.readlines()[-2:]
misses = int(misses.split(';')[0])
wall_secs = float(wall_secs)
print(f"cache-misses: {misses*1e-6/wall_secs}")
