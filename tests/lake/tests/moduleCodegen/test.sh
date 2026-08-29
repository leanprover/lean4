#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# This test covers `compiler.postponeCompile`, under which Lake defers a module system module's
# code generation to a separate `leanir` step producing its `.ir.sig`, `.ir`, and `.c`.
# ---

# The rebuild tests below edit the sources, so work on a copy
copy_to_work lakefile.toml Main.lean Test.lean Test Eval.lean

# Elaboration alone does not generate code
test_run build Test.A
test_exp ! -f .lake/build/ir/Test/A.c

# Each module's code generation is a job of its own
echo "# TEST: code generation"
test_out "Built Test.A:irArts" build Test.A:c -v
test_exp -f .lake/build/lib/lean/Test/A.ir.sig
test_exp -f .lake/build/lib/lean/Test/A.ir
test_out "Built Test.B:irArts" build Test.B:c -v
test_run build Test.C:c

# An import's IR must be provided even for a plain `import`, as the language server loads it
match_text 'Test/A.ir"' .lake/build/ir/Test/B.setup.json
match_text 'Test/A.ir"' .lake/build/ir/Test/B.irsetup.json

# The server allows `#eval` on a plainly imported definition, so it must be able to run it
echo "# TEST: server eval across a plain import"
echo '$' lake setup-file Eval.lean
"$LAKE" setup-file Eval.lean > eval.setup.json
test_cmd_eq 42 lean --setup eval.setup.json -DElab.inServer=true Eval.lean

# The generated code links and runs
echo "# TEST: link and run"
test_eq 42 exe codegen

# ---
# Tests that `leanir` is only rerun when needed
# ---

test_run build Test.A:c Test.B:c Test.C:c --no-build

# A non-inlinable definition's body is part of the module's IR, but not of its `.ir.sig`
echo "# TEST: irArts on a value edit"
test_cmd sed_i 's/n + n/n + n + 0/' Test/A.lean
test_out "Built Test.A:irArts" build Test.A:c -v
# importers read only the `.ir.sig`, so their own IR is unaffected
test_run build Test.B:c Test.C:c --no-build

# A new public definition changes the `.ir.sig` as well
echo "# TEST: irArts on an interface edit"
test_run build Test.A:c Test.B:c Test.C:c
test_cmd sed_i 's/^private def offset/public def extra : Nat := 7\nprivate def offset/' Test/A.lean
test_out "Built Test.A:irArts" build Test.A:c -v
test_out "Built Test.B:irArts" build Test.B:c -v
