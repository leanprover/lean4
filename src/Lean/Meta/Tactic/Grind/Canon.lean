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
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind
namespace Canon

/-!
A canonicalizer module for the `grind` tactic. The canonicalizer defined in `Meta/Canonicalizer.lean` is
not suitable for the `grind` tactic. It was designed for tactics such as `omega`, where the goal is
to detect when two structurally different atoms are definitionally equal.

The `grind` tactic, on the other hand, uses congruence closure. Moreover, types, type formers, proofs, and instances
are considered supporting elements and are not factored into congruence detection.

This module minimizes the number of `isDefEq` checks by comparing two terms `a` and `b` only if they are instances,
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

@[inline] private def get' : GoalM State :=
  return (← get).canon

@[inline] private def modify' (f : State → State) : GoalM Unit :=
  modify fun s => { s with canon := f s.canon }

/--
Helper function for `canonElemCore`. It tries `isDefEq a b` with default transparency, but using
at most `canonHeartbeats` heartbeats. It reports an issue if the threshold is reached.
Remark: `parent` is use only to report an issue.
-/
private def isDefEqBounded (a b : Expr) (parent : Expr) : GoalM Bool := do
  withCurrHeartbeats do
  let curr := (← getConfig).canonHeartbeats
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := curr*1000 }) do
      withDefault <| isDefEq a b)
    fun ex => do
      if ex.isRuntime then
        reportIssue m!"failed to show that{indentExpr a}\nis definitionally equal to{indentExpr b}\nwhile canonicalizing{indentExpr parent}\nusing `{curr}*1000` heartbeats, `(canonHeartbeats := {curr})`"
        return false
      else
        throw ex

/--
Helper function for canonicalizing `e` occurring as the `i`th argument of an `f`-application.
If `useIsDefEqBounded` is `true`, we try `isDefEqBounded` before returning false
-/
def canonElemCore (parent : Expr) (f : Expr) (i : Nat) (e : Expr) (useIsDefEqBounded : Bool) : GoalM Expr := do
  let s ← get'
  if let some c := s.canon.find? e then
    return c
  let key := (f, i)
  let eType ← inferType e
  let cs := s.argMap.find? key |>.getD []
  for (c, cType) in cs do
    -- We first check the typesr
    if (← withDefault <| isDefEq eType cType) then
      if (← isDefEq e c) then
        -- We used to check `c.fvarsSubset e` because it is not
        -- in general safe to replace `e` with `c` if `c` has more free variables than `e`.
        -- However, we don't revert previously canonicalized elements in the `grind` tactic.
        -- Moreover, we store the canonicalizer state in the `Goal` because we case-split
        -- and different locals are added in different branches.
        modify' fun s => { s with canon := s.canon.insert e c }
        trace_goal[grind.debugn.canon] "found {e} ===> {c}"
        return c
      if useIsDefEqBounded then
        -- If `e` and `c` are not types, we use `isDefEqBounded`
        if (← isDefEqBounded e c parent) then
          modify' fun s => { s with canon := s.canon.insert e c }
          trace_goal[grind.debugn.canon] "found using `isDefEqBounded`: {e} ===> {c}"
          return c
  trace_goal[grind.debug.canon] "({f}, {i}) ↦ {e}"
  modify' fun s => { s with canon := s.canon.insert e e, argMap := s.argMap.insert key ((e, eType)::cs) }
  return e

abbrev canonType (parent f : Expr) (i : Nat) (e : Expr) := withDefault <| canonElemCore parent f i e (useIsDefEqBounded := false)
abbrev canonInst (parent f : Expr) (i : Nat) (e : Expr) := withReducibleAndInstances <| canonElemCore parent f i e (useIsDefEqBounded := true)
abbrev canonImplicit (parent f : Expr) (i : Nat) (e : Expr) := withReducible <| canonElemCore parent f i e (useIsDefEqBounded := true)

/--
Return type for the `shouldCanon` function.
-/
private inductive ShouldCanonResult where
  | /- Nested types (and type formers) are canonicalized. -/
    canonType
  | /- Nested instances are canonicalized. -/
    canonInst
  | /- Implicit argument that is not an instance nor a type. -/
    canonImplicit
  | /-
    Term is not a proof, type (former), nor an instance.
    Thus, it must be recursively visited by the canonizer.
    -/
    visit
  deriving Inhabited

instance : Repr ShouldCanonResult where
  reprPrec r _ := match r with
    | .canonType => "canonType"
    | .canonInst => "canonInst"
    | .canonImplicit => "canonImplicit"
    | .visit => "visit"

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
    else if pinfo.isImplicit then
      if (← isTypeFormer arg) then
        return .canonType
      else
        return .canonImplicit
  if (← isProp arg) then
    return .visit
  else if (← isTypeFormer arg) then
    return .canonType
  else
    return .visit

unsafe def canonImpl (e : Expr) : GoalM Expr := do
  visit e |>.run' mkPtrMap
where
  visit (e : Expr) : StateRefT (PtrMap Expr Expr) GoalM Expr := do
    unless e.isApp || e.isForall do return e
    -- Check whether it is cached
    if let some r := (← get).find? e then
      return r
    let e' ← match e with
      | .app .. => e.withApp fun f args => do
        if f.isConstOf ``Lean.Grind.nestedProof && args.size == 2 then
          let prop := args[0]!
          let prop' ← visit prop
          if let some r := (← get').proofCanon.find? prop' then
            pure r
          else
            let e' := if ptrEq prop prop' then e else mkAppN f (args.set! 0 prop')
            modify' fun s => { s with proofCanon := s.proofCanon.insert prop' e' }
            pure e'
        else
          let pinfos := (← getFunInfo f).paramInfo
          let mut modified := false
          let mut args := args.toVector
          for h : i in [:args.size] do
            let arg := args[i]
            trace_goal[grind.debug.canon] "[{repr (← shouldCanon pinfos i arg)}]: {arg} : {← inferType arg}"
            let arg' ← match (← shouldCanon pinfos i arg) with
            | .canonType  => canonType e f i arg
            | .canonInst  => canonInst e f i arg
            | .canonImplicit => canonImplicit e f i (← visit arg)
            | .visit      => visit arg
            unless ptrEq arg arg' do
              args := args.set i arg'
              modified := true
          pure <| if modified then mkAppN f args.toArray else e
      | .forallE _ d b _ =>
        -- Recall that we have `ForallProp.lean`.
        let d' ← visit d
        -- Remark: users may not want to convert `p → q` into `¬p ∨ q`
        let b' ← if b.hasLooseBVars then pure b else visit b
        pure <| e.updateForallE! d' b'
      | _ => unreachable!
    modify fun s => s.insert e e'
    return e'

end Canon

/-- Canonicalizes nested types, type formers, and instances in `e`. -/
def canon (e : Expr) : GoalM Expr := do
  trace_goal[grind.debug.canon] "{e}"
  unsafe Canon.canonImpl e

end Lean.Meta.Grind
