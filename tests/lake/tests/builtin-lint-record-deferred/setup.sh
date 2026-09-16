#!/usr/bin/env bash
set -euo pipefail

# (Re)generate the pristine, un-annotated source that `--record-exceptions`
# edits in place. Regenerating on every run keeps the test idempotent: the
# checked-in tree never contains the recorded `set_option` lines, and a failed
# run cannot leave a mutated file behind to poison the next one.
cat > Violations.lean << 'EOF'
module

set_option doc.verso true

/-! First module docstring: {name (scope := "Init")}`Nat.firstMissingXYZ` does not resolve. -/

/-! Second module docstring: {name (scope := "Init")}`Nat.secondMissingXYZ` does not resolve. -/

/-- Declaration docstring: {name (scope := "Init")}`Nat.declMissingXYZ` does not resolve. -/
def declForwardRef : Nat := 0

/-- Resolvable declaration docstring: {name (scope := "Init")}`Nat.zero` resolves fine. -/
def goodForwardRef : Nat := 0
EOF
