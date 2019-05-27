#!/usr/bin/env python3

import re
import sys

lines = sys.stdin.readlines()
gc_millis = float(re.search(r"^\[GC\(([\d.]+)ms", lines[0])[1])
wall_secs = float(lines[1])
if not gc_millis:
    print("gc: 0.00001")
else:
    print(f"gc: {gc_millis*1e-3/wall_secs*100}")
