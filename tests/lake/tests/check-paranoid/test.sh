#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake check needs Linux namespaces"
  exit 0
fi

# User namespaces cannot be assumed available in CI containers; see `../fake-bwrap.sh`.
export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

# Both commands resolve dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first.
"$LAKE" resolve-deps

SYSROOT="$("$LAKE" env printenv LEAN_SYSROOT)"
BUNDLED=(leanchecker-paranoid lean4lean nanoda_bin con-leche)
KERNELS=("Lean paranoid" lean4lean nanoda con-leche)

# The real checkers are bundled into release toolchains only.
bundled=1
for exe in "${BUNDLED[@]}"; do
  [ -x "$SYSROOT/bin/$exe" ] || bundled=0
done
if [ $bundled = 1 ]; then
  test_status_out 0 'Uses axioms: Classical.choice, propext, Quot.sound' check --paranoid
  for kernel in "${KERNELS[@]}" "Lean default"; do
    match_text "$kernel kernel accepts the solution" produced.out
  done
  test_status_out 0 'Your solution is okay!' comparator --config config.json --paranoid
  for kernel in "${KERNELS[@]}" "Lean default"; do
    match_text "$kernel kernel accepts the solution" produced.out
  done
fi

# Everywhere else, point Lake at a copy of this toolchain whose bundled checkers are stubs that
# report what they were handed. Checkers run with a cleared environment, so the stubs are plain
# `sh`, and a marker file rather than a variable makes one reject.
STUB_SYSROOT="$PWD/work/sysroot"
mkdir -p "$STUB_SYSROOT/bin"
for f in "$SYSROOT"/*; do
  [ "${f##*/}" = bin ] || ln -s "$f" "$STUB_SYSROOT/"
done
for f in "$SYSROOT"/bin/*; do
  ln -s "$f" "$STUB_SYSROOT/bin/"
done
for exe in "${BUNDLED[@]}"; do
  rm -f "$STUB_SYSROOT/bin/$exe"
  cat > "$STUB_SYSROOT/bin/$exe" <<EOF
#!/bin/sh
echo "$exe stub got: \$*"
if [ $exe = nanoda_bin ]; then
  while IFS= read -r line || [ -n "\$line" ]; do echo "\$line"; done < "\$1"; echo
fi
[ ! -e "$PWD/work/reject-$exe" ]
EOF
  chmod +x "$STUB_SYSROOT/bin/$exe"
done
export LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT="$STUB_SYSROOT"

# `lake check` exports every axiom in scope, used or not, so a checker that polices axioms itself
# skips the ones not permitted and fails only on a use.
test_status_out 0 'Uses axioms: Classical.choice, propext, Quot.sound' check --paranoid
match_text 'leanchecker-paranoid stub got: --silent --from-export /' produced.out
match_text 'lean4lean stub got: --import /' produced.out
match_text 'nanoda_bin stub got: /' produced.out
match_text 'con-leche stub got: /' produced.out
match_text '"permitted_axioms":["propext","Classical.choice","Quot.sound"]' produced.out
match_text '"unpermitted_axiom_hard_error":false' produced.out
for kernel in "${KERNELS[@]}" "Lean default"; do
  match_text "$kernel kernel accepts the solution" produced.out
done

# `lake comparator` holds such a checker to the challenge's permitted axioms.
test_status_out 0 'Your solution is okay!' comparator --config config.json --paranoid
match_text '"permitted_axioms":["propext","Quot.sound","Classical.choice"]' produced.out
match_text '"unpermitted_axiom_hard_error":false' produced.out
for kernel in "${KERNELS[@]}" "Lean default"; do
  match_text "$kernel kernel accepts the solution" produced.out
done

# One rejection rejects the solution, and every other checker still reports.
touch work/reject-lean4lean
test_status_out 1 'lean4lean kernel rejected the solution' \
  comparator --config config.json --paranoid
match_text 'error: lean4lean exited with 1' produced.out
match_text 'nanoda kernel accepts the solution' produced.out
match_text 'con-leche kernel accepts the solution' produced.out
match_text 'Lean paranoid kernel accepts the solution' produced.out
match_text 'Lean default kernel accepts the solution' produced.out
rm work/reject-lean4lean

# Without `--paranoid`, only `leanchecker` runs.
test_status_out 0 'Lean default kernel accepts the solution' comparator --config config.json
no_match_text 'stub got:' produced.out

# A toolchain missing one of them fails the run rather than passing it with fewer checkers, and only
# with `--paranoid`.
rm "$STUB_SYSROOT/bin/leanchecker-paranoid"
test_status_out 1 'error: Lean paranoid exited with' comparator --config config.json --paranoid
test_status_out 0 'Lean default kernel accepts the solution' comparator --config config.json

rm -f produced.out
