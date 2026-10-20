#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake comparator needs Linux namespaces"
  exit 0
fi

export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

test_status_out 2 "'no-such.export' does not exist" \
  comparator --config config.json --challenge-from-export no-such.export

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
"$LAKE" build Challenge Solution Wrong
for mod in Challenge Solution Wrong; do
  "$LAKE" env leanexport "$mod" -- "${TARGETS[@]}" > "work/${mod}.export"
done

test_status_out 0 'Your solution is okay!' comparator --config config.json \
  --challenge-from-export work/Challenge.export --solution-from-export work/Solution.export
no_match_text 'Resolving dependencies' produced.out
no_match_text 'Building' produced.out
no_match_text 'Exporting' produced.out

test_status_out 1 'Challenge and solution theorem statement do not match' \
  comparator --config config.json \
  --challenge-from-export work/Challenge.export --solution-from-export work/Wrong.export

test_status_out 0 'Your solution is okay!' comparator --config config.json \
  --solution-from-export work/Solution.export
match_text 'Resolving dependencies' produced.out
match_text 'Building Challenge' produced.out
match_text 'Exporting' produced.out
no_match_text 'Building Solution' produced.out

rm -f produced.out
