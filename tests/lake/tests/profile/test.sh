#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Skip if samply is not installed
if ! command -v samply &>/dev/null; then
  echo "SKIP: samply not found"
  exit 0
fi

# Build the test executable
test_run build

# Test help output
test_out "lake profile" help profile
test_out "--rate" help profile
test_out "--raw" help profile
test_out "--no-serve" help profile

# Test --raw mode (records profile, skips symbolication/demangling)
lake_out profile --raw --output raw.json.gz hello || true
if match_text "samply record failed" produced.out 2>/dev/null; then
  echo "SKIP: samply cannot record (missing perf permissions?)"
  exit 0
fi

test_exp -f raw.json.gz
# Verify output is valid gzipped Firefox Profiler JSON
zcat raw.json.gz | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert 'threads' in d, f'missing threads key, got: {list(d.keys())}'
assert 'libs' in d, f'missing libs key, got: {list(d.keys())}'
print(f'raw profile: {len(d[\"threads\"])} threads, {len(d[\"libs\"])} libs')
"

# Test full pipeline (record + symbolicate + demangle, no serve)
test_run profile --no-serve --output demangled.json.gz hello
test_exp -f demangled.json.gz

# Verify demangled output structure
zcat demangled.json.gz | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert 'threads' in d, f'missing threads key'
assert 'libs' in d, f'missing libs key'
# Check that at least some strings exist in the profile
total_strings = 0
for t in d['threads']:
    sa = t.get('stringArray', [])
    total_strings += len(sa)
print(f'demangled profile: {len(d[\"threads\"])} threads, {total_strings} strings')
assert total_strings > 0, 'expected non-empty stringArray in profile threads'
"

# Cleanup
rm -f produced.out raw.json.gz demangled.json.gz
