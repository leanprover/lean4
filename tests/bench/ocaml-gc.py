#!/usr/bin/env python3

import sys
import json

lines = sys.stdin.readlines()
user_secs = float(lines[-1])
events = json.loads("\n".join(lines[:-1])[:-2] + "]")
starts = {}
gc_msecs = 0
for event in events:
    if event["name"] in ["minor", "major"]:
        tid = event["tid"]
        if event["ph"] == "B":
            if tid not in starts:
                starts[tid] = (event["name"], int(event["ts"]))
        elif tid in starts and starts[tid][0] == event["name"]:
            gc_msecs += int(event["ts"]) - starts[tid][1]
            del starts[tid]
print(f"gc: {gc_msecs*1e-6/user_secs*100}")
