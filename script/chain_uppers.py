#!/usr/bin/env python3
import re
import os
import sys

chain = re.compile(r"def ([\w.]+) .*:= ([\w.]+)", re.MULTILINE)
fpath = sys.argv[1]
uppers = set(s.strip() for s in open('script/u').readlines())
with open(fpath) as f:
    s = f.read()
for m in chain.findall(s):
    if m[1] in uppers:
        print(m[0])
