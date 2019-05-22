#!/usr/bin/env python3

import re
import sys

data = sys.stdin.read()
overheads = re.findall("([\d.]+)%", data)
gc_pc = sum(map(float, overheads))
print(f"gc: {gc_pc}")
