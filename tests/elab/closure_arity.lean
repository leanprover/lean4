module

meta import all Lean.Compiler.LCNF.EmitC
public meta import Lean.Elab.Command

/-!
Check the closure-arity limit in dynamic and static C emission using synthetic impure signatures.
This avoids elaborating a declaration with tens of thousands of dependent binders.
-/

open Lean Compiler LCNF
open Lean.Elab.Command

def closureArityTarget (n : Nat) : Nat := n
def closureArityGround : Nat := 0

meta def emitTestClosure (arity : Nat) (ground : Bool) : CoreM Unit := do
  let env ← getEnv
  try
    let param : Param .impure := {
      fvarId := ⟨`arg⟩, binderName := `arg, type := ImpureType.object, borrow := false }
    let signature : Signature .impure := {
      name := `closureArityTarget, levelParams := [], type := ImpureType.object,
      params := Array.replicate arity param }
    modifyEnv (impureSigExt.addEntry · signature)
    let action : EmitM Unit ← if ground then do
      modifyEnv (addSimpleGroundDecl · `closureArityGround (.pap `closureArityTarget #[]))
      let decl : Decl .impure := {
        name := `closureArityGround, levelParams := [], type := ImpureType.object,
        params := #[], value := .extern { entries := [] }, inlineAttr? := none }
      pure (emitGroundDecl decl "closure_arity_ground")
    else
      pure (emitLetDecl {
        fvarId := ⟨`closure⟩, binderName := `closure, type := ImpureType.object,
        value := .pap `closureArityTarget #[] })
    discard <| action.run { localDecls := #[], otherModuleDecls := #[], modName := `ClosureArity }
      |>.run {} |>.run (phase := .impure)
  finally
    setEnv env

run_cmd do
  for arity in [1, UInt16.size - 1] do
    for ground in [false, true] do
      liftCoreM <| emitTestClosure arity ground

/-- error: cannot create closure for 'closureArityTarget': arity 65536 exceeds the maximum of 65535 -/
#guard_msgs in
run_cmd liftCoreM <| emitTestClosure UInt16.size false

/-- error: cannot create closure for 'closureArityTarget': arity 65536 exceeds the maximum of 65535 -/
#guard_msgs in
run_cmd liftCoreM <| emitTestClosure UInt16.size true
