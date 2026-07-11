---
name: radar-results
description: Retrieve Lean benchmark (radar/speedcenter) results for a commit or PR as JSON and rank per-module regressions. Use when asked to analyze bench CI results, find the most affected modules/benchmarks, or compare two commits' performance.
allowed-tools: Bash
---

# Retrieving radar benchmark results

Benchmark CI results live on https://radar.lean-lang.org. The web UI is an SPA, but there is a
plain JSON API under `/api`.

## Finding the comparison hashes

The `leanprover-radar` bot posts a PR comment like:

> [Benchmark results](https://radar.lean-lang.org/repos/lean4/commits/COMMIT?reference=REFERENCE) for COMMIT against REFERENCE are in.

Fetch it with `gh api repos/leanprover/lean4/issues/<PR>/comments --jq '.[] | select(.user.login == "leanprover-radar") | .body'`.
The two hashes are the benched commit (`COMMIT`, usually the PR head) and the baseline (`REFERENCE`, usually the merge-base).

## Fetching the comparison

```bash
curl -s "https://radar.lean-lang.org/api/compare/lean4/<REFERENCE>/<COMMIT>/" -o cmp.json
```

(first path segment after `compare/` is the repo name; then baseline, then new commit.)

Top-level structure: `{chashFirst, chashSecond, comparison}`, where `comparison` has
`significant`, `warnings`, `notes`, `newMetrics`, `largeChanges`, `mediumChanges`, `smallChanges`,
and the full `measurements` array (~18k entries). Each measurement:

```json
{"metric": "build/module/Init.Data.Sum//instructions",
 "first": 0.49e9, "second": 1.21e9,
 "firstSource": "runner-lean1", "secondSource": "runner-lean1",
 "unit": null, "direction": -1}
```

`direction: -1` means lower is better. `first` = baseline value, `second` = new value.

## Useful metric families

- `build//instructions`, `build//cycles`, `build//wall-clock` — whole stdlib build totals.
- `build/module/<Module>//instructions|cycles` — per-module stdlib compile cost. Best signal for
  "which modules are most affected".
- `build/module/<Module>//bytes .olean|.olean.private|.olean.server|.ilean` — per-module artifact sizes.
- `misc/import <Module>//instructions`, `misc/re-elab <Module>//...` — import/re-elaboration benchmarks.
- `lake/...`, `other//...` — Lake and micro benchmarks.

## Ranking regressions

```bash
python3 - <<'EOF'
import json
ms = json.load(open('cmp.json'))['comparison']['measurements']
instr = [m for m in ms if m['metric'].endswith('//instructions') and m['first'] and m['second']]
for key, label in [(lambda m: m['second']/m['first'], 'ratio'),
                   (lambda m: m['second']-m['first'], 'absolute')]:
    instr.sort(key=key, reverse=True)
    print(f"top 15 by {label}:")
    for m in instr[:15]:
        print(f"  {m['metric']:70} {m['first']/1e9:10.2f}G -> {m['second']/1e9:10.2f}G  {m['second']/m['first']:.2f}x")
EOF
```

A near-constant absolute offset across many small modules points at per-compile overhead (e.g.
import-time work); a multiplicative factor on elaboration-heavy modules points at per-operation
cost (e.g. environment lookups).
