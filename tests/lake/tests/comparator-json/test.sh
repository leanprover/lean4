#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake comparator needs Linux namespaces"
  exit 0
fi

if ! command -v jq > /dev/null; then
  echo "Skipping test: jq not found"
  exit 0
fi

export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

"$LAKE" resolve-deps

STEPS='[.resolve_dependencies, .build_challenge, .export_challenge, .build_solution,
  .export_solution, .compare_statements, .check_axioms]'

# The report is all that is printed: nothing a child prints passes through.
test_status_json 0 comparator --json --config config.json
[ ! -s produced.err ]
match_json '.version == "0.1.0" and .judgement == "accepted" and .sandboxed == true'
match_json ".report | $STEPS | all(.judgement == \"success\")"
match_json '.report.kernel_reports | keys == ["Lean default"]'
match_json '.report.kernel_reports["Lean default"].judgement == "success"'
match_json '.report.config.solution_module == "Solution"'
# What a child writes to standard error is kept, here the warning of `fake-bwrap.sh`, but not the
# exporter's standard out, which is the export itself.
match_json '.report.build_solution.output.proc.stderr | contains("NOT REAL BWRAP")'
match_json '.report.export_solution.output.proc.stdout == ""'

# Without `--json`, the output is as before.
test_status_out 0 'Your solution is okay!' comparator --config config.json
match_text 'NOT REAL BWRAP' produced.out

# Each step that can fail does so on its own, and skips every step after it.

# `lake build` logs its failures to standard out.
test_status_json 1 comparator --json --config broken-challenge.json
[ ! -s produced.err ]
match_json '.judgement == "failure"'
match_json '.report.resolve_dependencies.judgement == "success"'
match_json '.report.build_challenge.judgement == "failure"'
match_json '.report.build_challenge.output.proc.stdout | contains("Broken.lean")'
match_json ".report | [$STEPS[] | .judgement] | .[2:] | all(. == \"skipped\")"
match_json '.report.kernel_reports["Lean default"].judgement == "skipped"'

test_status_json 1 comparator --json --config broken-solution.json
[ ! -s produced.err ]
match_json '.judgement == "failure"'
match_json '.report.build_challenge.judgement == "success"'
match_json '.report.export_challenge.judgement == "success"'
match_json '.report.build_solution.judgement == "failure"'
match_json '.report.build_solution.output.proc.stdout | contains("Broken.lean")'
match_json ".report | [$STEPS[] | .judgement] | .[4:] | all(. == \"skipped\")"
match_json '.report.kernel_reports["Lean default"].judgement == "skipped"'

test_status_json 1 comparator --json --config wrong.json
[ ! -s produced.err ]
match_json '.judgement == "failure"'
match_json '.report.export_solution.judgement == "success"'
match_json '.report.compare_statements.judgement == "failure"'
match_json '.report.compare_statements.output.str.string |
  contains("Challenge and solution theorem statement do not match")'
match_json '.report.check_axioms.judgement == "skipped"'
match_json '.report.kernel_reports["Lean default"].judgement == "skipped"'

test_status_json 1 comparator --json --config axiom.json
[ ! -s produced.err ]
match_json '.judgement == "failure"'
match_json '.report.compare_statements.judgement == "success"'
match_json '.report.check_axioms.judgement == "failure"'
match_json '.report.check_axioms.output.str.string | contains("helper")'
match_json '.report.kernel_reports["Lean default"].judgement == "skipped"'

# A kernel rejecting the solution does not stop the others.
test_status_json 1 comparator --json --config kernel.json
[ ! -s produced.err ]
match_json '.judgement == "failure"'
match_json ".report | $STEPS | all(.judgement == \"success\")"
match_json '.report.kernel_reports | keys == ["Lean default", "stub"]'
match_json '.report.kernel_reports.stub.judgement == "failure"'
match_json '.report.kernel_reports.stub.output.proc.stdout == "stub out\n"'
match_json '.report.kernel_reports.stub.output.proc.stderr | contains("stub err")'
match_json '.report.kernel_reports["Lean default"].judgement == "success"'

# Steps an export stands in for are skipped.
TARGETS=(
  comm
  propext Quot.sound Classical.choice
  Quot Quot.mk Quot.lift Quot.ind
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam
)
mkdir -p work
"$LAKE" build Solution
"$LAKE" env leanexport Solution -- "${TARGETS[@]}" > work/Solution.export
test_status_json 0 comparator --json --config config.json \
  --solution-from-export work/Solution.export
match_json '.report.resolve_dependencies.judgement == "success"'
match_json '.report.build_challenge.judgement == "success"'
match_json '.report.build_solution.judgement == "skipped"'
match_json '.report.export_solution.judgement == "skipped"'

# The report says the run was not sandboxed, in place of the warning.
test_status_json 0 comparator --json --config config.json --inadvisably-no-sandbox
[ ! -s produced.err ]
match_json '.judgement == "accepted" and .sandboxed == false'

# A run that cannot start has no report.
test_status_json 2 comparator --json --config no-such.json
[ ! -s produced.json ]
match_text 'could not read the configuration' produced.err

# The report tells kernels apart by name, so an external kernel cannot share one with a kernel Lake
# runs itself.
test_status_out 2 'the external kernel `nanoda` has the name of a kernel Lake runs itself' \
  comparator --config clash.json --paranoid

rm -f produced.out produced.json produced.err
