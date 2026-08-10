/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.MutualInductive

/-!
# The kernel's entry point into the certificate generators

`environment::add_inductive` asks for a certificate before it declares anything, since it takes the
recursors from it. A nested declaration is certified against the mutual model `NestedGen` builds; a
mutual one against the single family `MutualGen` collapses it to. Everything else is reported as
having no certificate, which is how the kernel learns to check and declare it itself.

The two compose without being composed here: the model `NestedGen` builds is a mutual block, so
declaring it comes back through this entry point and is reduced to a single family in turn.
-/

namespace Lean.Meta

open NestedGen (Certificate)

/--
Certify the declaration the kernel was handed, working from the declaration rather than from the
environment: the certificate has to be in hand before anything is declared.
-/
@[export lean_certify_inductive]
public def certifyInductive (kenv : Kernel.Environment) (d : Declaration) :
    IO (Except String (Option Certificate)) := do
  let .inductDecl lparams nparams types isUnsafe := d | return .ok none
  let types := types.toArray
  let some first := types[0]? | return .ok none
  let env ← Environment.ofKernelEnvForElab kenv {}
  let ctx : Core.Context := {
    fileName := "<inductive certificate>", fileMap := default
    options := Elab.async.set {} false, maxHeartbeats := 0
  }
  -- Purely syntactic and nothing is declared, so this is what every inductive pays to be routed.
  let detect := NestedGen.isNested lparams nparams types.toList
  let nested ← match ← ((MetaM.run' detect : CoreM Bool).run ctx { env }).toIO' with
    | .error ex => return .error (← ex.toMessageData.toString)
    | .ok (b, _) => pure b
  if nested then
    -- an unsafe declaration is not certified, so it needs none of the ingredients
    if !isUnsafe && NestedGen.ingredients.any fun n => !env.contains n then
      return .error "a nested inductive was declared before the certificate's ingredients exist"
    -- the fields the generator reads; the rest are only meaningful once the type exists
    let iv : InductiveVal := {
      name := first.name, levelParams := lparams, type := first.type, numParams := nparams
      numIndices := 0, all := types.toList.map (·.name), ctors := first.ctors.map (·.name)
      numNested := 0, isRec := true, isUnsafe, isReflexive := false }
    NestedGen.certifyCore env iv types id
  else if types.size ≥ 2 then
    MutualGen.certifyCore env lparams nparams types isUnsafe id
  else
    return .ok none

end Lean.Meta
