import Lean

/-!
Regression test for https://github.com/leanprover/lean4/issues/10577

Before the fix, the kernel would crash (access uninitialized memory) when a constant was applied
to the wrong number of universe levels.  The root cause was that `is_delta` could succeed for a
constant even when the supplied universe-level count did not match the declaration's level-parameter
count, but `unfold_definition` would subsequently return `none` for that same constant (because it
did contain the level-count check).  The call site in `lazy_delta_reduction_step` unconditionally
dereferenced the `unfold_definition` result, causing undefined behaviour.

The fix moves the level-parameter-count check into `is_delta`, establishing the invariant:
  **If `is_delta` succeeds then `unfold_definition` will also succeed.**
-/

-- Discovered via fuzzing; the important feature is that `false_of_true_eq_false`
-- (which has 0 universe-level parameters) is applied with 1 universe level in some
-- sub-expressions, while the surrounding declaration has `levelParams := []`.
def name_0 : Lean.Name := .anonymous
def level_0 : Lean.Level := .zero
def name_1 : Lean.Name := .str name_0 "false_of_true_eq_false"
def expr_0 : Lean.Expr := .lit (.natVal 0)
def expr_1 : Lean.Expr := .const name_1 [level_0]
def name_2 : Lean.Name := .str name_0 "Eq"
def expr_18 : Lean.Expr := .const name_2 [level_0]
def expr_8 : Lean.Expr := .letE `d (.bvar 0) (.bvar 0) (.bvar 0) false
def expr_10 : Lean.Expr := .const name_1 []
def expr_11 : Lean.Expr := .app expr_10 expr_8
def expr_13 : Lean.Expr := .app expr_18 expr_0
def expr_16 : Lean.Expr := .letE `c expr_11 (.bvar 0) (.bvar 0) false
def expr_27 : Lean.Expr := .app (.app expr_13 expr_1) expr_0
def expr_30 : Lean.Expr := .letE `b (.bvar 0) expr_27 expr_16 false
def expr_36 : Lean.Expr := .letE `a (.sort level_0) expr_10 expr_30 false
def decl_0 : Lean.Declaration :=
  .thmDecl {
    name := `foo42
    levelParams := []
    type := expr_36
    value := expr_10
  }

open Lean

/-- error: (kernel) let-declaration type mismatch 'a' -/
#guard_msgs in
run_meta
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore 0 decl_0 none)
