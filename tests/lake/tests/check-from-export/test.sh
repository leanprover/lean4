#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake check needs Linux namespaces"
  exit 0
fi

export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

test_status_out 2 "'no-such.export' does not exist" check --from-export no-such.export
test_status_out 2 "is a directory" check --from-export .

mkdir -p work
"$LAKE" build Solution Bad
"$LAKE" env leanexport Solution -- comm > work/solution.export
"$LAKE" env leanexport Bad -- bad > work/bad.export

test_status_out 0 'Lean default kernel accepts the solution' check --from-export work/solution.export
match_text 'Uses axioms: Classical.choice, propext, Quot.sound' produced.out
no_match_text 'Resolving dependencies' produced.out
no_match_text 'Building and exporting' produced.out

test_status_out 1 "Axiom 'sorryAx' is not permitted" check --from-export work/bad.export
match_text "it is used by 'bad'" produced.out

cd work
test_status_out 0 'Lean default kernel accepts the solution' check --from-export solution.export
no_match_text 'lake-manifest.json' produced.out
cd ..

rm -f produced.out
