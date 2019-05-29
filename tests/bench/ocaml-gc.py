#!/usr/bin/env python3

import sys

events = sys.stdin.readlines()
wall_secs = float(events[-1])
gc_nanos = 0
for event in events[::-1]:
    data = event.split()
    # see also https://gitlab.com/gasche/gc-latency-experiment/blob/master/parse_ocaml_log.ml
    if len(data) == 4 and data[0] == '@@' and data[3] == 'dispatch':
        gc_nanos += int(data[2]) - int(data[1])
print(f"gc: {gc_nanos*1e-9/wall_secs*100}")
