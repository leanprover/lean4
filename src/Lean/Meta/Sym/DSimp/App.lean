/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.DSimp.Result
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.ProofInstInfo
import Init.Omega
namespace Lean.Meta.Sym.DSimp
open Internal

/-!
# Simplifying Application Arguments

Unlike `Sym.Simp.App`, `dsimp` does not need to respect the congruence-info split
(`fixedPrefix`, `interlaced`, `congrTheorem`). That split exists in simp to make proof
construction efficient — but here there is no proof to build.

`dsimp` can rewrite *every* argument, subject only to the rules:
- **Skip proof arguments.** It is often a waste of time because of proof irrelevance.
In some cases, users may want to reduce proofs to eliminate dependencies. Users can
accomplish this by rewriting their own simproc.
- **Skip instance arguments.** Instances are not usually meaningful
  to simplify structurally. Moreover, we would be producing non-standard instances.

Both classes are read from `ProofInstInfo` (per-`declName`, cached in `SymM`). When the
head is not a `.const` (e.g. an `.fvar`-headed application), we have no signature info
and rewrite every argument.
-/

/--
Walks the application spine and `dsimp`s each argument unless `ProofInstInfo` marks it
as a proof or instance. The function head itself is not recursively simplified — atomic
heads (`.const`, `.fvar`) are no-ops anyway, and complex heads can be handled by
user-supplied `pre`/`post` simprocs.
-/
public def dsimpAppArgs (e : Expr) : DSimpM Result := do
  let numArgs := e.getAppNumArgs
  if h : numArgs = 0 then return .rfl
  let f := e.getAppFn
  let info? ← getProofInstInfoOfExpr? f
  let argsInfo? := info?.map (·.argsInfo)
  go argsInfo? numArgs e
where
  go (argsInfo? : Option (Array ProofInstArgInfo)) (i : Nat) (e : Expr) : DSimpM Result := do
    if i = 0 then return .rfl
    let .app f a := e | unreachable!
    let fr ← go argsInfo? (i - 1) f
    let skip : Bool :=
      match argsInfo? with
      | some ai =>
        if h : i - 1 < ai.size then
          let { isProof, isInstance } := ai[i - 1]
          isProof || isInstance
        else
          false  -- over-applied: no info, rewrite
      | none => false
    let ar ← if skip then pure .rfl else dsimp a
    match fr, ar with
    | .rfl _,     .rfl _     => return .rfl
    | .step f' _, .rfl _     => return .step (← e.updateAppS! f' a)
    | .rfl _,     .step a' _ => return .step (← e.updateAppS! f a')
    | .step f' _, .step a' _ => return .step (← e.updateAppS! f' a')

end Lean.Meta.Sym.DSimp
