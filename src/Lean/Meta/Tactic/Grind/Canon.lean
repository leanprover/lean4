/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic
import Lean.Meta.FunInfo
import Lean.Util.FVarSubset
import Lean.Util.PtrSet
import Lean.Util.FVarSubset

namespace Lean.Meta.Grind
namespace Canon

/-!
A canonicalizer module for the `grind` tactic. The canonicalizer defined in `Meta/Canonicalizer.lean` is
not suitable for the `grind` tactic. It was designed for tactics such as `omega`, where the goal is
to detect when two structurally different atoms are definitionally equal.

The `grind` tactic, on the other hand, uses congruence closure but disregards types, type formers, instances, and proofs.
Proofs are ignored due to proof irrelevance. Types, type formers, and instances are considered supporting
elements and are not factored into congruence detection. Instead, `grind` only checks whether
elements are structurally equal, which, in the context of the `grind` tactic, is equivalent to pointer equality.

This module minimizes the number of `isDefEq` checks by comparing two terms `a` and `b` only if they instances,
types, or type formers and are the `i`-th arguments of two different `f`-applications. This approach is
sufficient for the congruence closure procedure used by the `grind` tactic.

To further optimize `isDefEq` checks, instances are compared using `TransparencyMode.instances`, which reduces
the number of constants that need to be unfolded. If diagnostics are enabled, instances are compared using
the default transparency mode too for sanity checking, and discrepancies are reported.
Types and type formers are always checked using default transparency.
-/

structure State where
  argMap : PHashMap (Expr × Nat) (List Expr) := {}
  canon  : PHashMap Expr Expr := {}
  deriving Inhabited

/--
Helper function for canonicalizing `e` occurring as the `i`th argument of an `f`-application.
`isInst` is true if `e` is an type class instance.

Recall that we use `TransparencyMode.instances` for checking whether two instances are definitionally equal or not.
Thus, if diagnostics are enabled, we also check them using `TransparencyMode.default`. If the result is different
we report to the user.
-/
def canonElemCore (f : Expr) (i : Nat) (e : Expr) (isInst : Bool) : StateT State MetaM Expr := do
  let s ← get
  if let some c := s.canon.find? e then
    return c
  let key := (f, i)
  let cs := s.argMap.find? key |>.getD []
  for c in cs do
    if (← isDefEq e c) then
      if c.fvarsSubset e then
        -- It is not in general safe to replace `e` with `c` if `c` has more free variables than `e`.
        modify fun s => { s with canon := s.canon.insert e c }
        return c
    if isInst then
      if (← isDiagnosticsEnabled <&&> pure (c.fvarsSubset e) <&&> (withDefault <| isDefEq e c)) then
        -- TODO: consider storing this information in some structure that can be browsed later.
        trace[grind.issues] "the following `grind` static elements are definitionally equal with `default` transparency, but not with `instances` transparency{indentExpr e}\nand{indentExpr c}"
  modify fun s => { s with canon := s.canon.insert e e, argMap := s.argMap.insert key (e::cs) }
  return e

abbrev canonType (f : Expr) (i : Nat) (e : Expr) := withDefault <| canonElemCore f i e false
abbrev canonInst (f : Expr) (i : Nat) (e : Expr) := withReducibleAndInstances <| canonElemCore f i e true

/--
Return type for the `shouldCanon` function.
-/
private inductive ShouldCanonResult where
  | /-
    Nested proofs are ignored by the canonizer.
    That is, they are not canonized or recursively visited.
    -/
    ignore
  | /- Nested types (and type formers) are canonicalized. -/
    canonType
  | /- Nested instances are canonicalized. -/
    canonInst
  | /-
    Term is not a proof, type (former), nor an instance.
    Thus, it must be recursively visited by the canonizer.
    -/
    visit
  deriving Inhabited

/--
See comments at `ShouldCanonResult`.
-/
def shouldCanon (pinfos : Array ParamInfo) (i : Nat) (arg : Expr) : MetaM ShouldCanonResult := do
  if h : i < pinfos.size then
    let pinfo := pinfos[i]
    if pinfo.isInstImplicit then
      return .canonInst
    else if pinfo.isProp then
      return .ignore
  if (← isTypeFormer arg) then
    return .canonType
  else
    return .visit

unsafe def canonImpl (e : Expr) : StateT State MetaM Expr := do
  visit e |>.run' mkPtrMap
where
  visit (e : Expr) : StateRefT (PtrMap Expr Expr) (StateT State MetaM) Expr := do
    match e with
    | .bvar .. => unreachable!
    -- Recall that `grind` treats `let`, `forall`, and `lambda` as atomic terms.
    | .letE .. | .forallE .. | .lam ..
    | .const .. | .lit .. | .mvar .. | .sort .. | .fvar ..
    -- Recall that the `grind` preprocessor uses the `foldProjs` preprocessing step.
    | .proj ..
    -- Recall that the `grind` preprocessor uses the `eraseIrrelevantMData` preprocessing step.
    | .mdata ..  => return e
    -- We only visit applications
    | .app .. =>
      -- Check whether it is cached
      if let some r := (← get).find? e then
        return r
      e.withApp fun f args => do
        let pinfos := (← getFunInfo f).paramInfo
        let mut modified := false
        let mut args := args
        for i in [:args.size] do
          let arg := args[i]!
          let arg' ← match (← shouldCanon pinfos i arg) with
          | .ignore    => pure arg
          | .canonType => canonType f i arg
          | .canonInst => canonInst f i arg
          | .visit     => visit arg
          unless ptrEq arg arg' do
            args := args.set! i arg'
            modified := true
        let e' := if modified then mkAppN f args else e
        modify fun s => s.insert e e'
        return e'

/--
Canonicalizes nested types, type formers, and instances in `e`.
-/
def canon (e : Expr) : StateT State MetaM Expr :=
  unsafe canonImpl e

end Canon

end Lean.Meta.Grind
