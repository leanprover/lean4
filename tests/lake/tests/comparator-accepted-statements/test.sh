#!/usr/bin/env bash
source ../common.sh

./clean.sh

SANDBOX_ARGS=()
if [ "`uname`" = Linux ]; then
  export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"
else
  # These fixtures are trusted; exercise comparison on platforms without bwrap.
  SANDBOX_ARGS=(--inadvisably-no-sandbox)
fi
"$LAKE" resolve-deps
mkdir -p work
# The caller builds these trusted fixtures before entering the submitted workspace.
EVALUATOR="$(mktemp -d "$(cd .. && pwd)/comparator-reference.XXXXXX")"
trap 'rm -rf "$EVALUATOR"' EXIT
cp accepted.json "$EVALUATOR/accepted.json"
TARGETS=(
  propext Quot.sound Classical.choice Quot Quot.mk Quot.lift Quot.ind
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam And
)
APPROVALS=(
  Accepted.first Accepted.second Accepted.unused Accepted.notAProp Accepted.parameterized
  Accepted.polymorphic Accepted.withAxiom Accepted.withSorry
)
"$LAKE" build Task StatementTask DependencyTask Conditional
"$LAKE" env leanexport Task -- "${TARGETS[@]}" "${APPROVALS[@]}" task plain quantified supplied > "$EVALUATOR/Task.export"
"$LAKE" env leanexport StatementTask -- "${TARGETS[@]}" "${APPROVALS[@]}" task > "$EVALUATOR/StatementTask.export"
"$LAKE" env leanexport DependencyTask -- "${TARGETS[@]}" Accepted.first task > "$EVALUATOR/DependencyTask.export"

# The manifest path is relative to the configuration, not the working directory.
config() {
  COMPARATOR_ARGS=("${SANDBOX_ARGS[@]}" --challenge-from-export "$EVALUATOR/${4:-Task}.export")
  cat > "$EVALUATOR/config.json" <<EOF
{
  "challenge_module": "${4:-Task}",
  "solution_module": "$1",
  "theorem_names": [${2:-\"task\"}],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "accepted_statements_file": "${3:-accepted.json}"
}
EOF
}

config Conditional '"task", "plain", "quantified", "supplied"'
test_status_out 0 "Theorem 'task' matches conditional on: Accepted.second, Accepted.first" \
  comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
match_text "Theorem 'quantified' matches conditional on: Accepted.first" produced.out
match_text "Theorem 'supplied' matches conditional on: Accepted.first" produced.out
match_text 'Your solution matches conditional on the accepted statements listed above.' produced.out
no_match_text "Theorem 'plain' matches conditional" produced.out
no_match_text 'conditional on: Accepted.unused' produced.out
no_match_text 'Your solution is okay!' produced.out

config Direct
test_status_out 0 "conditional on: Accepted.first, Accepted.second" comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

config Bare
test_status_out 0 "conditional on: Accepted.first, Accepted.second" comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

config Unconditional
test_status_out 0 'Your solution is okay!' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
no_match_text 'conditional on:' produced.out

for module in Unlisted Disjunction Wrong; do
  config "$module"
  test_status_out 1 'Unaccepted conditional input or mismatched conclusion' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
done

config Changed
test_status_out 1 "Const does not match between challenge and target 'Accepted.first'" \
  comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

config Dependent
test_status_out 1 'Dependent conditional input is not supported' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

config StatementChanged '"task"' accepted.json StatementTask
test_status_out 1 "Const does not match between challenge and target 'ClaimMeaning'" \
  comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

echo '["Accepted.first"]' > "$EVALUATOR/one.json"
config DependencyChanged '"task"' one.json DependencyTask
test_status_out 1 "Const does not match between challenge and target 'Meaning'" \
  comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

for module in ForbiddenAxiom Sorry; do
  config "$module"
  test_status_out 1 'Illegal axiom detected' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
  no_match_text 'matches conditional on:' produced.out
done

# With no approved entries, the original exact comparison applies.
echo '[]' > "$EVALUATOR/empty.json"
config Direct '"task"' empty.json
test_status_out 1 'Challenge and solution theorem statement do not match' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

config Direct '"task"' missing.json
test_status_out 2 'could not read accepted statements' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
echo '{' > "$EVALUATOR/malformed.json"
config Direct '"task"' malformed.json
test_status_out 2 'malformed accepted statements' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
echo '["Accepted.first", "Accepted.first"]' > "$EVALUATOR/duplicate.json"
config Direct '"task"' duplicate.json
test_status_out 2 'duplicate accepted statement' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

echo '[""]' > "$EVALUATOR/empty-name.json"
config Direct '"task"' empty-name.json
test_status_out 2 'empty accepted statement name' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
echo '[42]' > "$EVALUATOR/wrong-type.json"
config Direct '"task"' wrong-type.json
test_status_out 2 'malformed accepted statements' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

echo '["Accepted.notAProp"]' > "$EVALUATOR/not-prop.json"
config Unconditional '"task"' not-prop.json
test_status_out 1 'must be a closed proposition definition' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

for name in Accepted.parameterized Accepted.polymorphic; do
  echo "[\"$name\"]" > "$EVALUATOR/invalid-definition.json"
  config Unconditional '"task"' invalid-definition.json
  test_status_out 1 'must be a closed proposition definition' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
done

for name in Accepted.withAxiom Accepted.withSorry; do
  echo "[\"$name\"]" > "$EVALUATOR/invalid-proof.json"
  config Unconditional '"task"' invalid-proof.json
  test_status_out 1 'Illegal axiom detected' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"
  no_match_text 'Your solution is okay!' produced.out
done

echo '["task"]' > "$EVALUATOR/target.json"
config Unconditional '"task"' target.json
test_status_out 1 'Accepted statement cannot be a comparison target' comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json"

# Exports use the same comparison and must report the same conditional result.
"$LAKE" env leanexport Conditional -- "${TARGETS[@]}" task plain quantified supplied > work/Conditional.export
config Conditional '"task", "plain", "quantified", "supplied"'
test_status_out 0 "Theorem 'task' matches conditional on: Accepted.second, Accepted.first" \
  comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/config.json" \
  --solution-from-export work/Conditional.export
no_match_text 'Building' produced.out
no_match_text 'Your solution is okay!' produced.out

# Removing the feature flag must reject this same conditional export.
cat > "$EVALUATOR/disabled.json" <<EOF
{
  "challenge_module": "Task",
  "solution_module": "Conditional",
  "theorem_names": ["task"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF
test_status_out 1 'Challenge and solution theorem statement do not match' \
  comparator "${COMPARATOR_ARGS[@]}" --config "$EVALUATOR/disabled.json" \
  --solution-from-export work/Conditional.export

rm -f produced.out
