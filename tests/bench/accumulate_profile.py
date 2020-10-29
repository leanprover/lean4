#!/usr/bin/env python3

import collections
import re
import sys

data = sys.stdin.read()
cats = collections.defaultdict(lambda: 0)
for m in re.findall("^([^\n\d]+)([\d.]+)(m?)s$", data, re.MULTILINE):
    cats[m[0].strip()] += float(m[1]) * (1e-3 if m[2] else 1)

for cat in sorted(cats.keys()):
    cat2 = cat
    if len(sys.argv) > 1:
        cat2 = f"{sys.argv[1]} {cat}"
    print(f"{cat2!r}: {cats[cat]:f}")
