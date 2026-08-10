#!/usr/bin/env bash
source ../common.sh

# Exercises the package-level code quality checks run by `lake lint --code-quality`:
# declarations of type `PackageCheck` tagged `@[package_code_quality_check]`, which the driver
# picks up from each lint target's import closure and runs once per target, against that
# target's environment. Additional checks modules can be imported alongside each target via
# `--checks` or the `checks` package configuration option. `Checks.lean` defines the checks
# imported by every target here; `Extra.lean` and `Failing.lean` each register one further
# check visible only in their own target.

./clean.sh

# Collects the emitted entries from `produced.out` into `produced.json`, one whitespace-free
# object per line, sorted so assertions do not depend on the order in which entries are emitted.
# Entries are pretty-printed across several lines (continuation lines are indented), while the
# interleaved build progress lines start with neither `{` nor whitespace.
collect_json() {
  awk '
    /^\{/ { if (buf != "") print buf; buf = $0; next }
    /^[ \t]/ { if (buf != "") { line = $0; sub(/^[ \t]+/, "", line); buf = buf line } next }
    { if (buf != "") { print buf; buf = "" } }
    END { if (buf != "") print buf }
  ' produced.out | tr -d ' ' | LC_ALL=C sort > produced.json
  cat produced.json
}

# Asserts that the second argument occurs exactly `count` times in the given file.
count_text() {
  count=$1; pat=$2; file=$3
  echo "? grep -c -F \"$pat\" $file = $count"
  actual="$(grep -c -F -- "$pat" "$file" || true)"
  if [ "$actual" = "$count" ]; then
    return 0
  else
    echo "FAILURE: found $actual occurrence(s), expected $count"
    return 1
  fi
}

# --- The registered checks run and their entries join the linter-derived ones. ---
lake_out lint --code-quality Pkg
collect_json
check_diff_core expected.json produced.json

# The properties the expected output encodes, spelled out:
# a check may report on a whole module or on a single declaration...
match_text '{"value":{"scalar":{"value":2}},"source":{"module":{"name":"Pkg"}},"name":"sizeMetric"}' produced.json
match_text '{"value":{"scalar":{"value":1}},"source":{"declaration":{"name":"answer","module":"Pkg"}},"name":"sizeMetric"}' produced.json
# ...and its value may be a dictionary rather than a scalar.
match_text '{"value":{"dict":{"dictionary":{"b":2,"a":1}}},"source":{"module":{"name":"Pkg"}},"name":"tallyMetric"}' produced.json
# The `srcSearchPath` handed to a check resolves the package's own sources (and only reports
# modules that exist).
match_text '{"value":{"dict":{"dictionary":{"Pkg.Sub":1,"Pkg.Nonexistent":0,"Pkg":1}}},"source":{"module":{"name":"Pkg"}},"name":"sourceFoundMetric"}' produced.json
# The `topLevelModule` handed to a check names the lint target.
match_text '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Pkg"}},"name":"topLevelMetric"}' produced.json
# A check can inspect the lint target's environment (`answer` is declared in `Pkg`).
match_text '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Pkg"}},"name":"envMetric"}' produced.json
# Linter-derived entries are emitted alongside the package checks' ones.
match_text '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Pkg"}},"name":"linter.unusedVariables"}' produced.json
# A check outside the target's import closure does not run.
no_match_text 'extraMetric' produced.json

# --- `--checks` imports the given modules alongside each lint target. ---
# `Extra` is not in `Pkg`'s import closure and has not been built yet, so this also covers
# building the checks module before importing it. `--checks` implies `--code-quality`.
lake_out lint --checks Extra Pkg
collect_json
count_text 1 '{"value":{"scalar":{"value":7}},"source":{"module":{"name":"Extra"}},"name":"extraMetric"}' produced.json
match_text '"name":"sizeMetric"' produced.json

# A checks module must resolve to a module of a workspace package.
if lake_out lint --checks Bogus Pkg; then
  echo "FAILURE: Lake unexpectedly succeeded"
  exit 1
fi
match_text 'unknown checks module `Bogus`' produced.out

# --- The `checks` package configuration option provides checks modules without a flag. ---
lake_out lint -f checks-config.toml --code-quality Pkg
collect_json
count_text 1 '{"value":{"scalar":{"value":7}},"source":{"module":{"name":"Extra"}},"name":"extraMetric"}' produced.json
# A module supplied both by the configuration and by `--checks` is imported only once.
lake_out lint -f checks-config.toml --checks Extra Pkg
collect_json
count_text 1 '{"value":{"scalar":{"value":7}},"source":{"module":{"name":"Extra"}},"name":"extraMetric"}' produced.json

# --- Multiple lint targets: the checks run once per target, on the target's environment. ---
lake_out lint --code-quality Pkg Extra
collect_json
# `sizeMetric` is registered in both targets' closures and contributes its two entries to each.
count_text 4 '"name":"sizeMetric"' produced.json
count_text 2 '"name":"tallyMetric"' produced.json
# The check registered only by `Extra` runs for that target alone.
count_text 1 '{"value":{"scalar":{"value":7}},"source":{"module":{"name":"Extra"}},"name":"extraMetric"}' produced.json
# `topLevelModule` distinguishes the two runs of the same check.
match_text '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Pkg"}},"name":"topLevelMetric"}' produced.json
match_text '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Extra"}},"name":"topLevelMetric"}' produced.json
# ...as do the environments the checks run against: `answer` is only visible from `Pkg`.
match_text '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Pkg"}},"name":"envMetric"}' produced.json
match_text '{"value":{"scalar":{"value":0}},"source":{"module":{"name":"Extra"}},"name":"envMetric"}' produced.json

# --- Package checks are independent of linter selection. ---
# Disabling every linter drops the linter-derived entries but leaves the checks' entries.
lake_out lint --code-quality --lint-only=-linter.all Pkg
collect_json
no_match_text 'linter.unusedVariables' produced.json
match_text '"name":"sizeMetric"' produced.json

# --- A failing check is reported on stderr and fails the run; the others still contribute. ---
if lake_out lint --code-quality Failing; then
  echo "FAILURE: Lake unexpectedly succeeded"
  exit 1
fi
match_text 'failingMetric has failed: boom' produced.out
collect_json
no_match_text 'failingMetric' produced.json
match_text '"name":"sizeMetric"' produced.json

# --- Package checks only run in code quality mode. ---
lake_out lint --builtin-lint Failing
no_match_text 'failingMetric' produced.out
no_match_text 'sizeMetric' produced.out
