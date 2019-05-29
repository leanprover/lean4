#!/usr/bin/env python3

import ast
import sys

info = dict(ast.literal_eval(sys.stdin.read().strip()))
gc_pc = float(info['GC_cpu_seconds']) / float(info['total_cpu_seconds']) * 100
print(f"gc: {gc_pc}")
