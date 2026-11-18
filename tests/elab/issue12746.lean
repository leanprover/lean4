import Lean

/-!
Regression test for #12746: `Nat`s that fit in `size_t` must not be truncated to 32 bits on their
way into the kernel's C++ code. Projection indices are covered by `kernelProjIdx.lean`.

`4294967296` is `2^32`, which truncates to `0`.
-/

open Lean

/-! Without truncation, these indices are beyond every loose bound variable in the expression. -/

/-- info: false -/
#guard_msgs in
#eval (mkBVar 0).hasLooseBVar 4294967296

/-- info: true -/
#guard_msgs in
#eval (mkBVar 0).hasLooseBVar 0

/-- info: Lean.Expr.bvar 0 -/
#guard_msgs in
#eval (mkBVar 0).liftLooseBVars 4294967296 1

/-- info: Lean.Expr.bvar 1 -/
#guard_msgs in
#eval (mkBVar 0).liftLooseBVars 0 1

/-- info: Lean.Expr.bvar 1 -/
#guard_msgs in
#eval (mkBVar 1).lowerLooseBVars 4294967297 1

/-- info: Lean.Expr.bvar 0 -/
#guard_msgs in
#eval (mkBVar 1).lowerLooseBVars 1 1

/-! The number of parameters of an inductive declaration is user input. -/

private def addInductive (name : Name) (numParams : Nat) (type : Expr) (ctors : List Constructor) : CoreM Unit := do
  let decl := Declaration.inductDecl [] numParams [{ name, type, ctors }] false
  let env ← ofExceptKernelException ((← getEnv).addDeclCore 0 0 decl none)
  IO.println s!"accepted with numParams = {(env.find? name).get!.inductiveVal!.numParams}"

/-- info: accepted with numParams = 0 -/
#guard_msgs in
#eval addInductive `Control (numParams := 0) (mkSort 1) []

/--
error: (kernel) invalid inductive datatype declaration, incorrect number of parameters
-/
#guard_msgs in
#eval addInductive `Wide0 (numParams := 4294967296) (mkSort 1) []

/--
error: (kernel) invalid inductive datatype declaration, incorrect number of parameters
-/
#guard_msgs in
#eval addInductive `Wide1 (numParams := 4294967297) (.forallE `x (mkSort 1) (mkSort 1) .default) []

/--
error: (kernel) invalid occurrence of datatype 'Wide2' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
#eval addInductive `Wide2 (numParams := 4294967296) (mkSort 1) [{ name := `Wide2.mk, type := mkConst `Wide2 }]
