#!/usr/bin/env bash
set -euo pipefail

# (Re)generate the pristine, un-annotated source that `--record-exceptions`
# edits in place. Regenerating on every run keeps the test idempotent: the
# checked-in tree never contains the recorded `set_option` lines, and a failed
# run cannot leave a mutated file behind to poison the next one.
cat > Violations.lean << 'EOF'
import Linters

-- Text linter (`linter.unusedVariables`, default-on): captured in `lintLogExt`
-- during the build and recorded via the entry's stored position.
def unusedVarHere : Nat :=
  let unusedLocal := 5
  3

-- Env linter (`linter.dummyMarker`, default-on): recorded via
-- `findDeclarationRanges?` + source-search-path lookup.
def fooDummyMarker : Nat := 42

-- Indented declaration: the recorded `set_option ... in` must inherit its
-- leading whitespace.
namespace Inner
  def nestedDummyMarker : Nat := 7
end Inner
EOF
