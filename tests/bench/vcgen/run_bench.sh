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
#   AddSubCancel(1000):   528.42 ms, 1 VCs by grind: 245.13 ms, kernel: 446.07 ms
# into JSONL measurements.
python3 -c "
import json, re, sys

for line in open('vcgen.out'):
    m = re.search(r'(\w+)\((\d+)\):\s+([0-9.]+) ms.*kernel:\s+([0-9.]+) ms', line)
    if not m:
        continue
    case, n, vcgen_ms, kernel_ms = m.group(1), m.group(2), m.group(3), m.group(4)
    for phase, val in [('vcgen', vcgen_ms), ('kernel', kernel_ms)]:
        print(json.dumps({
            'metric': f'vcgen/{case}/{n}/{phase}//wall-clock',
            'value': float(val) / 1000,
            'unit': 's'
        }))
" >> measurements.jsonl

rm -f vcgen.out
