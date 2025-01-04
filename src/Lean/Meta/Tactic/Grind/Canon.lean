/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
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

The `grind` tactic, on the other hand, uses congruence closure. Moreover, types, type formers, proofs, and instances
are considered supporting elements and are not factored into congruence detection.

This module minimizes the number of `isDefEq` checks by comparing two terms `a` and `b` only if they instances,
types, or type formers and are the `i`-th arguments of two different `f`-applications. This approach is
sufficient for the congruence closure procedure used by the `grind` tactic.

To further optimize `isDefEq` checks, instances are compared using `TransparencyMode.instances`, which reduces
the number of constants that need to be unfolded. If diagnostics are enabled, instances are compared using
the default transparency mode too for sanity checking, and discrepancies are reported.
Types and type formers are always checked using default transparency.

Remark:
The canonicalizer minimizes issues with non-canonical instances and structurally different but definitionally equal types,
but it does not solve all problems. For example, consider a situation where we have `(a : BitVec n)`
and `(b : BitVec m)`, along with instances `inst1 n : Add (BitVec n)` and `inst2 m : Add (BitVec m)` where `inst1`
and `inst2` are structurally different. Now consider the terms `a + a` and `b + b`. After canonicalization, the two
additions will still use structurally different (and definitionally different) instances: `inst1 n` and `inst2 m`.
Furthermore, `grind` will not be able to infer that  `HEq (a + a) (b + b)` even if we add the assumptions `n = m` and `HEq a b`.
-/

structure State where
  argMap     : PHashMap (Expr × Nat) (List Expr) := {}
  canon      : PHashMap Expr Expr := {}
  proofCanon : PHashMap Expr Expr := {}
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
      -- We used to check `c.fvarsSubset e` because it is not
      -- in general safe to replace `e` with `c` if `c` has more free variables than `e`.
      -- However, we don't revert previously canonicalized elements in the `grind` tactic.
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
      return .visit
  if (← isTypeFormer arg) then
    return .canonType
  else
    return .visit

unsafe def canonImpl (e : Expr) : StateT State MetaM Expr := do
  visit e |>.run' mkPtrMap
where
  visit (e : Expr) : StateRefT (PtrMap Expr Expr) (StateT State MetaM) Expr := do
    unless e.isApp || e.isForall do return e
    -- Check whether it is cached
    if let some r := (← get).find? e then
      return r
    let e' ← match e with
      | .app .. => e.withApp fun f args => do
        if f.isConstOf ``Lean.Grind.nestedProof && args.size == 2 then
          let prop := args[0]!
          let prop' ← visit prop
          if let some r := (← getThe State).proofCanon.find? prop' then
            pure r
          else
            let e' := if ptrEq prop prop' then e else mkAppN f (args.set! 0 prop')
            modifyThe State fun s => { s with proofCanon := s.proofCanon.insert prop' e' }
            pure e'
        else
          let pinfos := (← getFunInfo f).paramInfo
          let mut modified := false
          let mut args := args
          for i in [:args.size] do
            let arg := args[i]!
            let arg' ← match (← shouldCanon pinfos i arg) with
            | .canonType  => canonType f i arg
            | .canonInst  => canonInst f i arg
            | .visit      => visit arg
            unless ptrEq arg arg' do
              args := args.set! i arg'
              modified := true
          pure <| if modified then mkAppN f args else e
      | .forallE n d b bi =>
        -- Recall that we have `ForallProp.lean`.
        let d' ← visit d
        -- Remark: users may not want to convert `p → q` into `¬p ∨ q`
        let b' ← if b.hasLooseBVars then pure b else visit b
        if ptrEq d d' && ptrEq b b' then pure e else pure <| mkForall n bi d b
      | _ => unreachable!
    modify fun s => s.insert e e'
    return e'

/-- Canonicalizes nested types, type formers, and instances in `e`. -/
def canon (e : Expr) : StateT State MetaM Expr :=
  unsafe canonImpl e

end Canon

end Lean.Meta.Grind
