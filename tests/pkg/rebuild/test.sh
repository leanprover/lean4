#!/usr/bin/env bash
set -euxo pipefail

source ../../../src/lake/tests/common.sh

rm -rf .lake/build

mkdir -p Rebuild
cat <<EOF > Rebuild/Basic.lean
-- File autocreated by test.sh

module

public def hello := "world"

public def testSpec (xs : List Nat) : List Nat := xs.map (fun x => x + 1)

-- Public macro scopes such as from unnamed parameters and deriving handlers should not cause
-- rebuilds on changes above.
public def macroScopes : Nat -> Nat := id

public inductive Foo
deriving Repr
EOF

lake build

function test_unchanged() {
    # Keep around previous version for easier diffing.
    cp .lake/build/lib/lean/Rebuild/Basic.olean .lake
    lake build Rebuild.Basic
    lake build --no-build
}

# Whitespace does not matter.
echo "-- test" >> Rebuild/Basic.lean
test_unchanged

# Closed terms do not matter.
sed_i 's/"world"/"wodd"/' Rebuild/Basic.lean
test_unchanged

# Private declarations do not matter.
echo 'theorem priv : True := .intro' >> Rebuild/Basic.lean
test_unchanged

# Lambdas do not matter.
sed_i 's/"wodd"/dbg_trace "typo"; "wodd"/' Rebuild/Basic.lean
test_unchanged

# Private definitions do not matter.
echo 'def privd : Nat := 0' >> Rebuild/Basic.lean
test_unchanged

# Specializations do not matter.
sed_i 's/x + 1/x + 2/' Rebuild/Basic.lean
test_unchanged
