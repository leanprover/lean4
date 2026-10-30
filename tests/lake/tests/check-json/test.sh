#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake check needs Linux namespaces"
  exit 0
fi

if ! command -v jq > /dev/null; then
  echo "Skipping test: jq not found"
  exit 0
fi

export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

"$LAKE" resolve-deps

# The report is all that is printed: nothing a child prints passes through.
test_status_json 0 check --json
[ ! -s produced.err ]
match_json '.version == "0.1.0" and .judgement == "accepted" and .sandboxed == true'
match_json '.report.resolve_dependencies.judgement == "success"'
match_json '.report.build_report.judgement == "success"'
# The sandboxed half writes the export to standard out, which is not kept, and its log to standard
# error.
match_json '.report.build_report.output.proc.stdout == ""'
match_json '.report.build_report.output.proc.stderr | contains("NOT REAL BWRAP")'
match_json '.report.check_axioms.judgement == "success"'
match_json '.report.check_axioms.output.str.string ==
  "Uses axioms: propext, Classical.choice, Quot.sound"'
match_json '.report.kernel_reports | keys == ["Lean default"]'
match_json '.report.kernel_reports["Lean default"].judgement == "success"'

# Without `--json`, the output is as before.
test_status_out 0 'Uses axioms: propext, Classical.choice, Quot.sound' check
match_text 'Lean default kernel accepts the solution' produced.out

# Steps an export stands in for are skipped, and a failed step skips every step after it.
mkdir -p work
"$LAKE" build Bad
"$LAKE" env leanexport Bad -- bad > work/bad.export
test_status_json 1 check --json --from-export work/bad.export
[ ! -s produced.err ]
match_json '.judgement == "failure"'
match_json '.report.resolve_dependencies.judgement == "skipped"'
match_json '.report.build_report.judgement == "skipped"'
match_json '.report.check_axioms.judgement == "failure"'
match_json ".report.check_axioms.output.str.string | contains(\"Axiom 'sorryAx' is not permitted\")"
match_json '.report.kernel_reports["Lean default"].judgement == "skipped"'

# A build failure is reported with the build's log.
cd broken
"$LAKE" resolve-deps
test_status_json 1 check --json
[ ! -s produced.err ]
match_json '.judgement == "failure"'
match_json '.report.resolve_dependencies.judgement == "success"'
match_json '.report.build_report.judgement == "failure"'
match_json '.report.build_report.output.proc.stderr | contains("Broken.lean")'
match_json '.report.check_axioms.judgement == "skipped"'
cd ..

# The report says the run was not sandboxed, in place of the warning.
test_status_json 0 check --json --inadvisably-no-sandbox
[ ! -s produced.err ]
match_json '.judgement == "accepted" and .sandboxed == false'

rm -f produced.out produced.json produced.err broken/produced.json broken/produced.err
