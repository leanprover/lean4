#!/usr/bin/env bash
source ../common.sh

# This suite exercises Linux namespace enforcement, never the fake test wrapper.
if [ "$(uname)" != Linux ] || ! command -v bwrap >/dev/null; then
  if [ "${COMPARATOR_REQUIRE_SANDBOX_TESTS:-0}" = 1 ]; then
    echo 'Real bubblewrap is required for evaluator isolation tests' >&2
    exit 1
  fi
  echo 'Skipping evaluator isolation tests: Linux and bubblewrap required'
  exit 0
fi
export COMPARATOR_BWRAP="$(command -v bwrap)"
"$COMPARATOR_BWRAP" --version
"$COMPARATOR_BWRAP" --ro-bind / / --unshare-all -- /bin/true

./clean.sh
copy_to_work evaluator project
ROOT="$PWD"
cd evaluator
"$LAKE" build Reference
TARGETS=(
  success protectedTarget Evaluator.approved And
  propext Quot.sound Classical.choice Quot Quot.mk Quot.lift Quot.ind
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam
)
"$LAKE" env leanexport Reference -- "${TARGETS[@]}" > reference.export
echo '["Evaluator.approved"]' > accepted.json
cd ../project
# Never execute the adversarial lakefile outside the sandbox, even for setup.
cp ../evaluator/lake-manifest.json lake-manifest.json
mkdir -p .lake
touch .lake/poison
ln ../evaluator/reference.export .lake/reference-link
echo '["Project.only"]' > accepted.json
config() {
  cat > ../evaluator/config.json <<EOF
{"challenge_module":"Reference","solution_module":"$1",
 "theorem_names":["${2:-success}"],
 "permitted_axioms":["propext","Quot.sound","Classical.choice"],
 "accepted_statements_file":"accepted.json"}
EOF
  cp ../evaluator/config.json comparator.json
  sha256sum ../evaluator/config.json ../evaluator/accepted.json ../evaluator/reference.export > ../expected.sha256
}
compare() {
  test_status_out "$1" "$2" comparator --config ../evaluator/config.json \
    --challenge-from-export ../evaluator/reference.export
  sha256sum --check ../expected.sha256
  no_match_text 'protected-write-succeeded:' produced.out
}

config Good
# The feature must fail closed before any project code without an independent reference.
test_status_out 2 'accepted statements require --challenge-from-export' \
  comparator --config ../evaluator/config.json
no_match_text 'Resolving dependencies' produced.out
sha256sum --check ../expected.sha256

compare 3 'conditional on: Evaluator.approved'
for name in config.json accepted.json reference.export; do
  match_text "protected-write-denied: $name" produced.out
  match_text "protected-write-denied: symlink $name" produced.out
done
match_text 'private-build-write-succeeded' produced.out
match_text 'protected-write-denied: compilation' produced.out
test -f .lake/poison
cmp .lake/reference-link ../evaluator/reference.export

config AliasSpoof
compare 1 "Const does not match between challenge and target 'Evaluator.approved'"
config TargetSpoof protectedTarget
compare 1 "Const does not match between challenge and target 'ClaimMeaning'"
config Extra
compare 1 'Unaccepted conditional input or mismatched conclusion'

config Good
echo 'not an export' > ../evaluator/malformed.export
test_status_out 2 'could not parse evaluator challenge export' \
  comparator --config ../evaluator/config.json --challenge-from-export ../evaluator/malformed.export
no_match_text 'Resolving dependencies' produced.out
test_status_out 2 'evaluator configuration must be outside the solution project' \
  comparator --config comparator.json --challenge-from-export ../evaluator/reference.export
cp ../evaluator/reference.export .lake/local.export
test_status_out 2 'evaluator challenge export must be outside the solution project' \
  comparator --config ../evaluator/config.json --challenge-from-export .lake/local.export
ln -s "$PWD/.lake/local.export" ../evaluator/linked.export
test_status_out 2 'evaluator challenge export must be outside the solution project' \
  comparator --config ../evaluator/config.json --challenge-from-export ../evaluator/linked.export
ln -s "$PWD/accepted.json" ../evaluator/linked.json
sed 's/"accepted.json"/"linked.json"/' ../evaluator/config.json > ../evaluator/linked-config.json
test_status_out 2 'evaluator accepted statements must be outside the solution project' \
  comparator --config ../evaluator/linked-config.json --challenge-from-export ../evaluator/reference.export

# A submission cannot turn the one writable mount into the evaluator directory.
mv .lake saved-cache
ln -s "$ROOT/evaluator" .lake
test_status_out 2 'solution .lake must not be a symbolic link' \
  comparator --config ../evaluator/config.json --challenge-from-export ../evaluator/reference.export
sha256sum --check ../expected.sha256
rm .lake
mv saved-cache .lake
echo 'Real sandbox evaluator isolation tests passed'
