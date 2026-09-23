#!/usr/bin/env bash
source ../common.sh

# Exercises `lake lint --code-quality`: instead of reporting linter warnings,
# each one is emitted as a JSON code quality entry on stdout. Covers three
# entry sources:
#   * text linters (`linter.unusedVariables`), aggregated per module into one
#     entry whose scalar value is the warning count,
#   * env linters (`linter.dummyMarker`, defined in `Linters.lean`), emitted per
#     flagged declaration together with the module defining it, and
#   * entries recorded during elaboration (`Linters.lean`), persisted into the
#     `.olean` per module and emitted verbatim: `declCommands` is recorded via
#     `logCodeQualityEntryIf` and attributed to `linter.declMetric`, so linter
#     selection flags apply to it; `declCommandsRaw` is recorded via
#     `logCodeQualityEntry` without attribution, so no selection flag can
#     suppress it.
# The first two flavours key their entry on the linter's *option* name; recorded
# entries carry a free-form metric name, with the producing linter's option name
# (if any) stored alongside internally, which `--lint-only` filters on.

./clean.sh

# Collects the emitted entries from `produced.out` into `produced.json`, one
# whitespace-free object per line, sorted so assertions do not depend on the
# order in which entries are emitted. Entries are pretty-printed across several
# lines (continuation lines are indented), while the interleaved build progress
# lines start with neither `{` nor whitespace.
collect_json() {
  awk '
    /^\{/ { if (buf != "") print buf; buf = $0; next }
    /^[ \t]/ { if (buf != "") { line = $0; sub(/^[ \t]+/, "", line); buf = buf line } next }
    { if (buf != "") { print buf; buf = "" } }
    END { if (buf != "") print buf }
  ' produced.out | tr -d ' ' | LC_ALL=C sort > produced.json
  cat produced.json
}

# Asserts that `pat` occurs exactly `count` times in the given file.
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

# --- Baseline: in report mode the same violations are reported and fail. ---
lake_out lint --builtin-lint Violations || true
match_pat 'Variable name `unusedLocal` is not explicitly referenced' produced.out
match_pat 'Variable name `alsoUnusedLocal` is not explicitly referenced' produced.out
match_pat 'Variable name `unusedInSub` is not explicitly referenced' produced.out
match_pat "fooDummyMarker declaration name ends with 'DummyMarker'" produced.out
match_pat "Inner.nestedDummyMarker declaration name ends with 'DummyMarker'" produced.out
match_pat "subDummyMarker declaration name ends with 'DummyMarker'" produced.out

# --- Code quality mode. ---
# `--code-quality` implies `--builtin-lint` and succeeds (exit 0) even though
# violations were found: the entries are data, not failures.
lake_out lint --code-quality Violations
collect_json
check_diff_core expected.json produced.json

# The properties the expected output encodes, spelled out:
# the two `unusedVariables` warnings in `Violations` are aggregated into one
# entry with a count of 2...
match_text '{"value":{"scalar":{"value":2}},"source":{"module":{"name":"Violations"}},"name":"linter.unusedVariables"}' produced.json
# ...while the one in the imported `Violations.Sub` is attributed to that module.
match_text '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Violations.Sub"}},"name":"linter.unusedVariables"}' produced.json
# Env linter findings are per declaration, tagged with their defining module.
match_text '{"value":{"scalar":{"value":1}},"source":{"declaration":{"name":"fooDummyMarker","module":"Violations"}},"name":"linter.dummyMarker"}' produced.json
match_text '{"value":{"scalar":{"value":1}},"source":{"declaration":{"name":"subDummyMarker","module":"Violations.Sub"}},"name":"linter.dummyMarker"}' produced.json
# A declaration-level `set_option linter.dummyMarker false in` is honored.
no_match_text 'suppressedDummyMarker' produced.json
# Recorded entries are emitted verbatim, one per declaration command per module: four in
# `Violations` (the `set_option ... in`-wrapped declaration is not a `declaration` command)
# and two in `Violations.Sub`.
count_text 4 '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Violations"}},"name":"declCommands"}' produced.json
count_text 2 '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Violations.Sub"}},"name":"declCommands"}' produced.json
count_text 4 '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Violations"}},"name":"declCommandsRaw"}' produced.json
count_text 2 '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Violations.Sub"}},"name":"declCommandsRaw"}' produced.json
# Nothing outside the linted package leaks in (`Linters.lean` defines the linters).
no_match_text '"module":"Linters"' produced.json
no_match_text '"name":"Linters"' produced.json

# --- Linter selection. ---
# `--lint-only` restricts the output to the explicitly enabled linters. Recorded entries are
# filtered by the linter option name persisted with each entry, so the default-on
# `linter.declMetric` entries (recorded during the build) are dropped too; the unattributed
# `declCommandsRaw` entries are exempt from the filter and survive.
lake_out lint --code-quality --lint-only=linter.dummyMarker Violations
collect_json
match_text 'fooDummyMarker' produced.json
no_match_text 'linter.unusedVariables' produced.json
no_match_text '"declCommands"' produced.json
match_text 'declCommandsRaw' produced.json

# ...and explicitly enabling the recording linter keeps its entries.
lake_out lint --code-quality --lint-only=linter.declMetric Violations
collect_json
match_text '"declCommands"' produced.json
no_match_text 'linter.unusedVariables' produced.json
no_match_text 'fooDummyMarker' produced.json

# Disabling a default-on linter drops its entries; the env linter and the recorded
# entries still report.
lake_out lint --code-quality --linters=-linter.unusedVariables Violations
collect_json
no_match_text 'linter.unusedVariables' produced.json
match_text 'fooDummyMarker' produced.json
match_text '"declCommands"' produced.json

# Disabling the recording linter suppresses recording of the gated entries at elaboration
# time; the unattributed entries are still recorded.
lake_out lint --code-quality --linters=-linter.declMetric Violations
collect_json
no_match_text '"declCommands"' produced.json
match_text 'declCommandsRaw' produced.json
match_text 'linter.unusedVariables' produced.json

# --- Multiple lint targets. ---
# `Violations.Sub` sits in the import closure of both targets, but its recorded entries are
# collected only once.
lake_out lint --code-quality Violations Violations.Sub
collect_json
count_text 2 '{"value":{"scalar":{"value":1}},"source":{"module":{"name":"Violations.Sub"}},"name":"declCommands"}' produced.json

# --- No enabled linters means no linter entries. ---
# Only the unattributed recorded entries remain: they are not tied to any linter option, so
# `-linter.all` cannot suppress them.
lake_out lint --code-quality --lint-only=-linter.all Violations
collect_json
count_text 6 '"name":"declCommandsRaw"' produced.json
no_match_text '"declCommands"' produced.json
no_match_text 'linter.unusedVariables' produced.json
no_match_text 'dummyMarker' produced.json
