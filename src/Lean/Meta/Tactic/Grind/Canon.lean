/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Util
import Lean.Meta.FunInfo
import Lean.Util.FVarSubset
import Lean.Meta.IntInstTesters
import Lean.Meta.NatInstTesters
import Lean.Meta.Tactic.Grind.SynthInstance
public section
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
Furthermore, `grind` will not be able to infer that  `a + a ≍ b + b` even if we add the assumptions `n = m` and `a ≍ b`.
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
      isDefEqD a b)
    fun ex => do
      if ex.isRuntime then
        reportIssue! "failed to show that{indentExpr a}\nis definitionally equal to{indentExpr b}\nwhile canonicalizing{indentExpr parent}\nusing `{curr}*1000` heartbeats, `(canonHeartbeats := {curr})`"
        return false
      else
        throw ex

/--
Helper function for canonicalizing `e` occurring as the `i`th argument of an `f`-application.
If `useIsDefEqBounded` is `true`, we try `isDefEqBounded` before returning false.

Remark: `isInst` is `true` if element is an instance.
-/
private def canonElemCore (parent : Expr) (f : Expr) (i : Nat) (e : Expr) (useIsDefEqBounded : Bool) (isInst := false) : GoalM Expr := do
  let s ← get'
  let key := { f, i, arg := e : CanonArgKey }
  /-
  **Note**: We used to use `s.canon.find? e` instead of `s.canonArg.find? key`. This was incorrect.
  First, for types and implicit arguments, we recursively visit `e` before invoking this function.
  Thus, `s.canon.find? e` always returns some value `c`, causing us to miss possible canonicalization opportunities.
  Moreover, `e` may be the argument of two different `f` functions.
  -/
  if let some c := s.canonArg.find? key then
    return c
  let c ← go
  modify' fun s => { s with canonArg := s.canonArg.insert key c }
  return c
where
  checkDefEq (e c : Expr) : GoalM Bool := do
    if (← isDefEq e c) then
      -- We used to check `c.fvarsSubset e` because it is not
      -- in general safe to replace `e` with `c` if `c` has more free variables than `e`.
      -- However, we don't revert previously canonicalized elements in the `grind` tactic.
      -- Moreover, we store the canonicalizer state in the `Goal` because we case-split
      -- and different locals are added in different branches.
      modify' fun s => { s with canon := s.canon.insert e c }
      trace_goal[grind.debug.canon] "found {e} ===> {c}"
      return true
    if useIsDefEqBounded then
      -- If `e` and `c` are not types, we use `isDefEqBounded`
      if (← isDefEqBounded e c parent) then
        modify' fun s => { s with canon := s.canon.insert e c }
        trace_goal[grind.debug.canon] "found using `isDefEqBounded`: {e} ===> {c}"
        return true
    return false

  go : GoalM Expr := do
    let eType ← inferType e
    if isInst then
      /-
      **Note**: Recall that some `grind` modules (e.g., `lia`) rely on instances defined directly in core.
      This test ensures we use them as the canonical representative.
      -/
      if let some c := getBuiltinInstance? eType then
        if (← checkDefEq e c) then
          return c
    let s ← get'
    let key := (f, i)
    let cs := s.argMap.find? key |>.getD []
    for (c, cType) in cs do
      /-
      We first check the types
      The following checks are a performance bottleneck.
      For example, in the test `grind_ite.lean`, there are many checks of the form:
      ```
      w_4 ∈ assign.insert v true → Prop =?= w_1 ∈ assign.insert v false → Prop
      ```
      where `grind` unfolds the definition of `DHashMap.insert` and `TreeMap.insert`.
      -/
      if (← isDefEqD eType cType) then
        if (← checkDefEq e c) then
          return c
    trace_goal[grind.debug.canon] "({f}, {i}) ↦ {e}"
    modify' fun s => { s with canon := s.canon.insert e e, argMap := s.argMap.insert key ((e, eType)::cs) }
    return e

private abbrev canonType (parent f : Expr) (i : Nat) (e : Expr) :=
  withDefault <| canonElemCore parent f i e (useIsDefEqBounded := false)

private abbrev canonInst (parent f : Expr) (i : Nat) (e : Expr) :=
  withReducibleAndInstances <| canonElemCore parent f i e (useIsDefEqBounded := true) (isInst := true)

private abbrev canonImplicit (parent f : Expr) (i : Nat) (e : Expr) :=
  withReducible <| canonElemCore parent f i e (useIsDefEqBounded := true)

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
    Thus, it must be recursively visited by the canonicalizer.
    -/
    visit
  deriving Inhabited

private instance : Repr ShouldCanonResult where
  reprPrec r _ := private match r with
    | .canonType => "canonType"
    | .canonInst => "canonInst"
    | .canonImplicit => "canonImplicit"
    | .visit => "visit"

/--
See comments at `ShouldCanonResult`.
-/
private def shouldCanon (pinfos : Array ParamInfo) (i : Nat) (arg : Expr) : MetaM ShouldCanonResult := do
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

/--
Returns `true` if `shouldCannon pinfos i arg` is not `.visit`.
This is a helper function used to implement mbtc.
-/
def isSupport (pinfos : Array ParamInfo) (i : Nat) (arg : Expr) : MetaM Bool := do
  let r ← shouldCanon pinfos i arg
  return !r matches .visit

/--
Auxiliary function for normalizing the arguments of `OfNat.ofNat` during canonicalization.
This is needed because satellite solvers create `Nat` and `Int` numerals using the
APIs `mkNatLit` and `mkIntLit`, which produce terms of the form
`@OfNat.ofNat Nat <num> inst` and `@OfNat.ofNat Int <num> inst`.
This becomes a problem when a term in the input goal has already been canonicalized
and its type is not exactly `Nat` or `Int`. For example, in issue #9477, we have:
```
structure T where
upper_bound : Nat
def T.range (a : T) := 0...a.upper_bound
theorem range\_lower (a : T) : a.range.lower = 0 := by rfl
```
Here, the `0` in `range_lower` is actually represented as:
```
(@OfNat.ofNat
  (Std.PRange.Bound (Std.PRange.RangeShape.lower (Std.PRange.RangeShape.mk Std.PRange.BoundShape.closed Std.PRange.BoundShape.open)) Nat)
  (nat_lit 0)
  (instOfNatNat (nat_lit 0)))
```
Without this normalization step, the satellite solver would need to handle multiple
representations for `(0 : Nat)` and `(0 : Int)`, complicating reasoning.
-/
-- Remark: This is not a great solution. We should consider writing a custom canonicalizer for
-- `OfNat.ofNat` and other constants with built-in support in `grind`.
private def normOfNatArgs? (args : Array Expr) : MetaM (Option (Array Expr)) := do
  if h : args.size = 3 then
    let mut args : Vector Expr 3 := h ▸ args.toVector
    let mut modified := false
    if args[1].isAppOf ``OfNat.ofNat then
      -- If nested `OfNat.ofNat`, convert to raw nat literal
      let some val ← getNatValue? args[1] | pure ()
      args := args.set 1 (mkRawNatLit val)
      modified := true
    let inst := args[2]
    if (← Structural.isInstOfNatNat inst) && !args[0].isConstOf ``Nat then
      return some (args.set 0 Nat.mkType |>.toArray)
    else if (← Structural.isInstOfNatInt inst) && !args[0].isConstOf ``Int then
      return some (args.set 0 Int.mkType |>.toArray)
    else if modified then
      return some args.toArray
  return none

@[export lean_grind_canon]
partial def canonImpl (e : Expr) : GoalM Expr := do profileitM Exception "grind canon" (← getOptions) do
  trace_goal[grind.debug.canon] "{e}"
  visit e |>.run' {}
where
  visit (e : Expr) : StateRefT (Std.HashMap ExprPtr Expr) GoalM Expr := do
    unless e.isApp || e.isForall do return e
    -- Check whether it is cached
    if let some r := (← get).get? { expr := e } then
      return r
    let e' ← match e with
      | .app .. => e.withApp fun f args => do
        if f.isConstOf ``Grind.nestedProof && args.size == 2 then
          let prop := args[0]!
          let prop' ← visit prop
          if let some r := (← get').proofCanon.find? prop' then
            pure r
          else
            let e' := if isSameExpr prop prop' then e else mkAppN f (args.set! 0 prop')
            modify' fun s => { s with proofCanon := s.proofCanon.insert prop' e' }
            pure e'
        else if f.isConstOf ``Grind.nestedDecidable && args.size == 2 then
          let prop := args[0]!
          let prop' ← visit prop
          let e' := if isSameExpr prop prop' then e else mkAppN f (args.set! 0 prop')
          pure e'
        else
          let mut modified := false
          let args ← if f.isConstOf ``OfNat.ofNat then
            let some args ← normOfNatArgs? args | pure args
            modified := true
            pure args
          else
            pure args
          let pinfos := (← getFunInfo f).paramInfo
          let mut args := args.toVector
          for h : i in *...args.size do
            let arg := args[i]
            trace_goal[grind.debug.canon] "[{repr (← shouldCanon pinfos i arg)}]: {arg} : {← inferType arg}"
            let arg' ← match (← shouldCanon pinfos i arg) with
              | .canonType =>
                /-
                The type may have nested propositions and terms that may need to be canonicalized too.
                So, we must recurse over it. See issue #10232
                -/
                canonType e f i (← visit arg)
              | .canonImplicit => canonImplicit e f i (← visit arg)
              | .visit => visit arg
              | .canonInst =>
                if arg.isAppOfArity ``Grind.nestedDecidable 2 then
                  let prop := arg.appFn!.appArg!
                  let prop' ← visit prop
                  if isSameExpr prop prop' then pure arg else pure (mkApp2 arg.appFn!.appFn! prop' arg.appArg!)
                else
                  canonInst e f i arg
            unless isSameExpr arg arg' do
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
    modify fun s => s.insert { expr := e } e'
    return e'

end Canon

end Lean.Meta.Grind
