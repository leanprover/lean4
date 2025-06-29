#!/usr/bin/env python3

import collections
import re
import sys

cats = collections.defaultdict(lambda: 0)
for line in sys.stdin:
    if m := re.match(r"(.+?) ([\d.]+)(m?)s", line) or \
            re.match(r"\s*(number of imported bytes|number of imported consts|number of imported entries):\s+(\d+)()", line):
        cats[m[1].strip()] += float(m[2]) * (1e-3 if m[3] else 1)
    sys.stderr.write(line)

for cat in sorted(cats.keys()):
    cat2 = cat
    if len(sys.argv) > 1:
        cat2 = f"{sys.argv[1]} {cat}"
    print(f"{cat2!r}: {cats[cat]:f}")
