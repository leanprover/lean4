#!/usr/bin/env bash
source ../common.sh

# Exercises `lake lint --code-quality`: instead of reporting linter warnings,
# each one is emitted as a JSON code quality entry on stdout. Covers both linter
# flavours:
#   * text linters (`linter.unusedVariables`), aggregated per module into one
#     entry whose scalar value is the warning count, and
#   * env linters (`linter.dummyMarker`, defined in `Linters.lean`), emitted per
#     flagged declaration together with the module defining it.
# Both flavours key their entry on the linter's *option* name.

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
# Nothing outside the linted package leaks in (`Linters.lean` defines the linter).
no_match_text '"module":"Linters"' produced.json

# --- Linter selection. ---
# `--lint-only` restricts the output to the explicitly enabled linters.
lake_out lint --code-quality --lint-only=linter.dummyMarker Violations
collect_json
match_text 'fooDummyMarker' produced.json
no_match_text 'linter.unusedVariables' produced.json

# Disabling a default-on linter drops its entries; the env linter still reports.
lake_out lint --code-quality --linters=-linter.unusedVariables Violations
collect_json
no_match_text 'linter.unusedVariables' produced.json
match_text 'fooDummyMarker' produced.json

# --- No violations means no entries. ---
lake_out lint --code-quality --lint-only=-linter.all Violations
collect_json
test_cmd test ! -s produced.json
