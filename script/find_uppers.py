#!/usr/bin/env python3
import regex as re
import os
import sys

upper = re.compile(r"^\s*(?:namespace|class|structure|inductive) ((?!inductive)[\w.]+)|(?:def|constant) ([\w.]+).*: Type$", re.MULTILINE)
fpath = sys.argv[1]
with open(fpath) as f:
    s = f.read()
for m in upper.findall(s):
    for n in m:
        if n not in ('and', 'or'):
            for part in n.split('.'):
                if part:
                    print(part)
