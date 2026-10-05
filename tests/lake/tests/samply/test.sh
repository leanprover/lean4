#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Keep generated profiles and helper executables in the ignored work directory.
copy_to_work Main.lean lakefile.toml lean-toolchain
trap 'rm -f produced.out ./*.json.gz' EXIT

test_run build
test_out "lake samply" help samply
test_out "--raw" help samply
test_out "--no-serve" help samply

if [ "$OS" != Windows_NT ]; then
  mkdir -p bin
  cp ../mock-samply.py bin/samply
  chmod +x bin/samply
  (
    export PATH="$PWD/bin:$PATH"
    args=(hello -- --rate 123 -- "an argument with spaces" --flag)
    test_run samply --raw -o raw.json.gz "${args[@]}"
    test_run samply --no-serve -o "demangled profile.json.gz" "${args[@]}"
    test_cmd python3 ../check-profile.py "demangled profile.json.gz"
    test_cmd python3 ../check-serving.py "$LAKE" -- --rate 123 -- "an argument with spaces" --flag
    SAMPLY_TEST_RESPONSE=short test_err "symbolication returned the wrong number of frames" samply --no-serve "${args[@]}"
    SAMPLY_TEST_RESPONSE=http-error test_err "curl" samply --no-serve "${args[@]}"
    echo keep > preserved.json.gz
    SAMPLY_TEST_FAIL=1 test_err "samply record failed (exit 17)" samply --raw -o preserved.json.gz "${args[@]}"
    test_cmd_eq keep cat preserved.json.gz
  )
fi

# Probe perf support independently, so a Lake regression cannot become a skip.
if ! command -v samply &>/dev/null; then
  echo "SKIP: real samply not found (deterministic tests passed)"
  exit 0
fi
if ! samply record --save-only -o probe.json.gz -- .lake/build/bin/hello >produced.out 2>&1; then
  if grep -Ei 'perf_event_open|perf_event_paranoid|Operation not permitted|Permission denied' produced.out; then
    echo "SKIP: samply lacks profiling permissions (deterministic tests passed)"
    exit 0
  fi
  cat produced.out
  exit 1
fi

# Test --raw mode (records profile, skips symbolication/demangling).
# `-- --rate 100` exercises the samply-arg forwarding path.
test_run samply --raw -o raw.json.gz hello -- --rate 100
test_exp -f raw.json.gz
# Verify output is valid gzipped Firefox Profiler JSON
gzip -dc raw.json.gz | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert 'threads' in d, f'missing threads key, got: {list(d.keys())}'
assert 'libs' in d, f'missing libs key, got: {list(d.keys())}'
print(f'raw profile: {len(d[\"threads\"])} threads, {len(d[\"libs\"])} libs')
"

# Test full pipeline (record + symbolicate + demangle, no serve)
test_run samply --no-serve -o demangled.json.gz hello
test_exp -f demangled.json.gz

# Verify demangled output structure
gzip -dc demangled.json.gz | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert 'threads' in d, f'missing threads key'
assert 'libs' in d, f'missing libs key'
assert d['meta']['symbolicated'] is True
# Check that at least some strings exist in the profile
total_strings = 0
for t in d['threads']:
    sa = t.get('stringArray', [])
    total_strings += len(sa)
print(f'demangled profile: {len(d[\"threads\"])} threads, {total_strings} strings')
assert total_strings > 0, 'expected non-empty stringArray in profile threads'
assert any(s.startswith('work') for t in d['threads'] for s in t['stringArray']), 'missing demangled work function'
"

if [ "$OS" != Windows_NT ]; then
  test_cmd python3 ../check-serving.py "$LAKE"
fi
