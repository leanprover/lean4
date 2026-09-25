import Lean

open Lean

set_option Elab.async false

/-!
Reproducer for the reference-count overflow of #14383. Actual reproduction needs `depth` bump below
and ~12GB of free RAM.

`maxDag` builds a `Level` DAG that expands to `2 ^ depth` occurrences of a single shared leaf, so
checking a declaration whose type mentions it drives that leaf object's 32-bit reference count past
`INT_MAX`. The wrapped count corrupts the object, and the kernel accepts `Candidate.{u} : Enc.{u}.val`
even though the proof only establishes `Enc.{0}.val`; `Candidate.{1}` then yields `False`.
-/

namespace RCOverflow

def AllSubsingleton.{u} : Prop :=
  ∀ (α : Sort u) (x y : α), x = y

opaque Enc.{u} : { p : Prop // p = AllSubsingleton.{u} } :=
  ⟨AllSubsingleton.{u}, rfl⟩

theorem encSpec.{u} : Enc.{u}.val = AllSubsingleton.{u} :=
  Enc.{u}.property

theorem allZero : AllSubsingleton.{0} := by
  intro α x y
  rfl

theorem encZero : Enc.{0}.val :=
  Eq.mpr encSpec.{0} allZero

theorem encOneFalse (value : Enc.{1}.val) : False :=
  Bool.noConfusion ((Eq.mp encSpec.{1} value) Bool false true)

private def candidateName := `RCOverflow.Candidate

private def falseName := `RCOverflow.false

--private def depth := 30
private def depth := 12

private def maxDag (leaf : Level) : Nat → Level
  | 0 => leaf
  | depth + 1 => let previous := maxDag leaf depth; Level.max previous previous

private def paddingTree (first : Nat) : Nat → Expr
  | 0 => mkRawNatLit first
  | depth + 1 => mkApp2 (mkConst ``Nat.add)
      (paddingTree first depth) (paddingTree (first + 2^depth) depth)

private def targetType (dag : Level) (paddingDepth : Nat) : Expr :=
  mkLet `u (mkConst ``PUnit [dag]) (mkConst ``PUnit.unit [dag])
    (mkLet `padding (mkConst ``Nat) (paddingTree 1 paddingDepth)
      (mkProj ``Subtype 0 (mkConst ``Enc [dag])) true) true

private def perform (env : Environment) (depth paddingDepth : Nat) :
    IO (Except Kernel.Exception Environment) := do
  let declaration : Declaration := .thmDecl {
    name := candidateName, levelParams := [`u]
    type := targetType (maxDag (Level.param `u) depth) paddingDepth
    value := mkConst ``encZero }
  return env.addDeclCore 0 4000 declaration none

end RCOverflow

run_meta do
  let task ← IO.asTask (RCOverflow.perform (← getEnv) RCOverflow.depth 13) Task.Priority.dedicated
  let .ok candidate := task.get | throwError "dedicated task failed"
  let .ok env := candidate | return
  let falseDecl : Declaration := .thmDecl {
    name := RCOverflow.falseName, levelParams := []
    type := mkConst ``False
    value := mkApp (mkConst ``RCOverflow.encOneFalse)
      (mkConst RCOverflow.candidateName [Level.one]) }
  let .ok env := env.addDeclCore 0 4000 falseDecl none
    | throwError "candidate accepted, but `False` was rejected"
  setEnv env
  logInfo m!"`False` accepted with axioms {← collectAxioms RCOverflow.falseName}"
