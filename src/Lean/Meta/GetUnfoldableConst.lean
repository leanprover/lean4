/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
public import Lean.Meta.Match.MatchPatternAttr
public section
namespace Lean.Meta

/--
Implements the `TransparencyMode` hierarchy for unfolding decisions.
See `TransparencyMode` and `ReducibilityStatus` for the design rationale.
-/
def canUnfoldDefault (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  match cfg.transparency with
  | .none => return false
  | .all  => return true
  | .default => return !(← isIrreducible info.name)
  | m =>
    let status ← getReducibilityStatus info.name
    if status == .reducible then
      return true
    else if status == .instanceReducible && (m == .instances || m == .implicit) then
      return true
    else if status == .implicitReducible && m == .implicit then
      return true
    else
      return false

/--
Alternative can-unfold predicate used inside `whnfMatcher`.
See module comment above `unfoldNestedDIte` in `Lean.Meta.WHNF`.
-/
def canUnfoldAtMatcher (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  if (← canUnfoldDefault cfg info) then
    return true
  /- Beyond what the normal transparency allows, we additionally unfold
     certain definitions to expose constructors in match discriminants. -/
  if hasMatchPatternAttribute (← getEnv) info.name then
    return true
  return info.name == ``OfNat.ofNat -- needed to reduce numeric literals in match discriminants
   || info.name == ``NatCast.natCast -- needed for `↑m` in match discriminants (pervasive in Int proofs)
   || info.name == ``Zero.zero || info.name == ``One.one -- needed for `0`/`1` in match discriminants
   || info.name == ``decEq
   || info.name == ``Nat.decEq
   || info.name == ``Char.ofNat   || info.name == ``Char.ofNatAux
   || info.name == ``String.decEq || info.name == ``List.hasDecEq
   || info.name == ``Fin.ofNat -- needed for Fin literal reduction in match discriminants
   || info.name == ``UInt8.ofNat  || info.name == ``UInt8.decEq
   || info.name == ``UInt16.ofNat || info.name == ``UInt16.decEq
   || info.name == ``UInt32.ofNat || info.name == ``UInt32.decEq
   || info.name == ``UInt64.ofNat || info.name == ``UInt64.decEq
   /- `Fin.ofNat` reduces to `⟨a % n, _⟩`, so we also need to unfold `%` (i.e., `HMod.hMod`
      and `Mod.mod`) to expose the `Fin.mk` constructor in match discriminants. -/
   || info.name == ``HMod.hMod || info.name == ``Mod.mod

def canUnfold (info : ConstantInfo) : MetaM Bool := do
  let ctx ← read
  let cfg ← getConfig
  match ctx.customCanUnfoldPredicate? with
  | some f => f cfg info
  | none =>
    match ctx.config.canUnfoldPredicateConfig with
    | .default => canUnfoldDefault cfg info
    | .atMatcher => canUnfoldAtMatcher cfg info

/--
Look up a constant name, returning the `ConstantInfo`
if it is a def/theorem that should be unfolded at the current reducibility settings,
or `none` otherwise.

This is part of the implementation of `whnf`.
External users wanting to look up names should be using `Lean.getConstInfo`.
-/
def getUnfoldableConst? (constName : Name) : MetaM (Option ConstantInfo) := do
  let some ainfo := (← getEnv).findAsync? constName | throwUnknownConstantAt (← getRef) constName
  match ainfo.kind with
  | .thm => return none
  | .defn => if (← canUnfold ainfo.toConstantInfo) then return ainfo.toConstantInfo else return none
  | _ => return none

/--
As with `getUnfoldableConst?` but return `none` instead of failing if the constant is not found.
-/
def getUnfoldableConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (.thmInfo _)          => return none
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some (.axiomInfo _)       => recordUnfoldAxiom constName; return none
  | _                         => return none

end Meta
