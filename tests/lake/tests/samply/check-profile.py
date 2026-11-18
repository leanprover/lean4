"""Check symbolication without corrupting shared labels or losing thread mappings."""
import gzip
import json
import sys

with gzip.open(sys.argv[1], "rt") as inp:
    profile = json.load(inp)
assert profile["meta"]["symbolicated"] is True
first, second = profile["threads"]
assert first["stringArray"][0] == "shared label"
names = [first["stringArray"][i] for i in first["funcTable"]["name"]]
assert names == [f"Test.f{i}" for i in range(20000)] + ["shared label"], names[:10]
assert second["stringArray"][second["funcTable"]["name"][0]] == "Test.f7"
