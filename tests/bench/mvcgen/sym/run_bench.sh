rm -f measurements.jsonl

# Build dependencies first so their compilation isn't measured.
lake build Cases Driver Baseline

# Run benchmarks single-threaded for reproducible measurements.
# Use `capture` instead of piping through `tee` so that build failures are not masked.
LEAN_NUM_THREADS=1 capture lake build VCGenBench
cat "$CAPTURED.out.produced" > vcgen.out
LEAN_NUM_THREADS=1 capture lake build BaselineBench
cat "$CAPTURED.out.produced" >> vcgen.out

# Parse lines like:
#   AddSubCancel(1000):   528 ms, 1 VCs by grind: 245 ms, kernel: 446 ms
# into JSONL measurements.
python3 -c "
import json, re, sys

for line in open('vcgen.out'):
    m = re.search(r'(\w+)\((\d+)\):\s+(\d+) ms.*kernel:\s+(\d+) ms', line)
    if not m:
        continue
    case, n, vcgen_ms, kernel_ms = m.group(1), m.group(2), m.group(3), m.group(4)
    for phase, val in [('vcgen', vcgen_ms), ('kernel', kernel_ms)]:
        print(json.dumps({
            'metric': f'mvcgen/sym/{case}/{n}/{phase}//wall-clock',
            'value': int(val) / 1000,
            'unit': 's'
        }))
" >> measurements.jsonl

rm -f vcgen.out
