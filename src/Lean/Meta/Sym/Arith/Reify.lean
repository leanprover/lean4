/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Functions
public import Lean.Meta.Sym.Arith.MonadVar
public import Lean.Meta.Sym.LitValues
public section
namespace Lean.Meta.Sym.Arith
open Sym.Arith (MonadCanon)

/-!
# Reification of arithmetic expressions

Converts Lean expressions into `CommRing.Expr` (ring) or `CommSemiring.Expr`
(semiring) for reflection-based normalization.

Instance validation uses pointer equality (`isSameExpr`) against cached function
expressions from `Functions.lean`.

## Differences from grind's `Reify.lean`

- Uses `MonadMkVar` for variable creation instead of grind's `internalize` + `mkVarCore`
- Uses `Sym.getNatValue?`/`Sym.getIntValue?` (pure) instead of `MetaM` versions
- No `MonadSetTermId` — term-to-ring-id tracking is grind-specific
-/

section RingReify

variable [MonadLiftT SymM m] [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m] [MonadRing m] [MonadMkVar m]

def isAddInst (inst : Expr) : m Bool :=
  return isSameExpr (← getAddFn).appArg! inst
def isMulInst (inst : Expr) : m Bool :=
  return isSameExpr (← getMulFn).appArg! inst
def isSubInst (inst : Expr) : m Bool :=
  return isSameExpr (← getSubFn).appArg! inst
def isNegInst (inst : Expr) : m Bool :=
  return isSameExpr (← getNegFn).appArg! inst
def isPowInst (inst : Expr) : m Bool :=
  return isSameExpr (← getPowFn).appArg! inst
def isIntCastInst (inst : Expr) : m Bool :=
  return isSameExpr (← getIntCastFn).appArg! inst
def isNatCastInst (inst : Expr) : m Bool :=
  return isSameExpr (← getNatCastFn).appArg! inst

private def reportRingAppIssue [MonadLiftT SymM m] (e : Expr) : m Unit := do
  reportIssue! "ring term with unexpected instance{indentExpr e}"

/--
Converts a Lean expression `e` into a `RingExpr`.

If `skipVar` is `true`, returns `none` if `e` is not an interpreted ring term
(used for equalities/disequalities). If `false`, treats non-interpreted terms
as variables (used for inequalities).
-/
partial def reifyRing? (e : Expr) (skipVar : Bool := true) : m (Option RingExpr) := do
  let toVar (e : Expr) : m RingExpr := do
    return .var (← mkVar e)
  let asVar (e : Expr) : m RingExpr := do
    reportRingAppIssue e
    return .var (← mkVar e)
  let rec go (e : Expr) : m RingExpr := do
    match_expr e with
    | HAdd.hAdd _ _ _ i a b =>
      if (← isAddInst i) then return .add (← go a) (← go b) else asVar e
    | HMul.hMul _ _ _ i a b =>
      if (← isMulInst i) then return .mul (← go a) (← go b) else asVar e
    | HSub.hSub _ _ _ i a b =>
      if (← isSubInst i) then return .sub (← go a) (← go b) else asVar e
    | HPow.hPow _ _ _ i a b =>
      let some k := Sym.getNatValue? b |>.run | toVar e
      if (← isPowInst i) then return .pow (← go a) k else asVar e
    | Neg.neg _ i a =>
      if (← isNegInst i) then return .neg (← go a) else asVar e
    | IntCast.intCast _ i a =>
      if (← isIntCastInst i) then
        let some k := Sym.getIntValue? a |>.run | toVar e
        return .intCast k
      else
        asVar e
    | NatCast.natCast _ i a =>
      if (← isNatCastInst i) then
        let some k := Sym.getNatValue? a |>.run | toVar e
        return .natCast k
      else
        asVar e
    | OfNat.ofNat _ n _ =>
      /-
      **Note**: We extract `n` directly as a raw nat literal. The grind version uses `MetaM`'s
      `getNatValue?` which handles multiple encodings (raw literals, nested `OfNat`, etc.).
      In `SymM`, we assume terms have been canonicalized by `Sym.canon` before reification,
      so `OfNat.ofNat _ n _` always has a raw nat literal at position 1.
      -/
      let .lit (.natVal k) := n | toVar e
      return .num k
    | BitVec.ofNat _ n =>
      let .lit (.natVal k) := n | toVar e
      return .num k
    | _ => toVar e
  let toTopVar (e : Expr) : m (Option RingExpr) := do
    if skipVar then
      return none
    else
      return some (← toVar e)
  let asTopVar (e : Expr) : m (Option RingExpr) := do
    reportRingAppIssue e
    toTopVar e
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if (← isAddInst i) then return some (.add (← go a) (← go b)) else asTopVar e
  | HMul.hMul _ _ _ i a b =>
    if (← isMulInst i) then return some (.mul (← go a) (← go b)) else asTopVar e
  | HSub.hSub _ _ _ i a b =>
    if (← isSubInst i) then return some (.sub (← go a) (← go b)) else asTopVar e
  | HPow.hPow _ _ _ i a b =>
    let some k := Sym.getNatValue? b |>.run | asTopVar e
    if (← isPowInst i) then return some (.pow (← go a) k) else asTopVar e
  | Neg.neg _ i a =>
    if (← isNegInst i) then return some (.neg (← go a)) else asTopVar e
  | IntCast.intCast _ i a =>
    if (← isIntCastInst i) then
      let some k := Sym.getIntValue? a |>.run | toTopVar e
      return some (.intCast k)
    else
      asTopVar e
  | NatCast.natCast _ i a =>
    if (← isNatCastInst i) then
      let some k := Sym.getNatValue? a |>.run | toTopVar e
      return some (.natCast k)
    else
      asTopVar e
  | OfNat.ofNat _ n _ =>
    let .lit (.natVal k) := n | asTopVar e
    return some (.num k)
  | _ => toTopVar e

end RingReify

section SemiringReify

variable [MonadLiftT SymM m] [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m] [MonadSemiring m] [MonadMkVar m]

private def reportSemiringAppIssue [MonadLiftT SymM m] (e : Expr) : m Unit := do
  reportIssue! "semiring term with unexpected instance{indentExpr e}"

/--
Converts a Lean expression `e` into a `SemiringExpr`.
Only recognizes `add`, `mul`, `pow`, `natCast`, and numerals (no `sub`, `neg`, `intCast`).
-/
partial def reifySemiring? (e : Expr) : m (Option SemiringExpr) := do
  let toVar (e : Expr) : m SemiringExpr := do
    return .var (← mkVar e)
  let asVar (e : Expr) : m SemiringExpr := do
    reportSemiringAppIssue e
    return .var (← mkVar e)
  let rec go (e : Expr) : m SemiringExpr := do
    match_expr e with
    | HAdd.hAdd _ _ _ i a b =>
      if isSameExpr (← getAddFn').appArg! i then return .add (← go a) (← go b) else asVar e
    | HMul.hMul _ _ _ i a b =>
      if isSameExpr (← getMulFn').appArg! i then return .mul (← go a) (← go b) else asVar e
    | HPow.hPow _ _ _ i a b =>
      let some k := Sym.getNatValue? b |>.run | toVar e
      if isSameExpr (← getPowFn').appArg! i then return .pow (← go a) k else asVar e
    | NatCast.natCast _ i a =>
      if isSameExpr (← getNatCastFn').appArg! i then
        let some k := Sym.getNatValue? a |>.run | toVar e
        return .num k
      else
        asVar e
    | OfNat.ofNat _ n _ =>
      let .lit (.natVal k) := n | toVar e
      return .num k
    | _ => toVar e
  let toTopVar (e : Expr) : m (Option SemiringExpr) := do
    return some (← toVar e)
  let asTopVar (e : Expr) : m (Option SemiringExpr) := do
    reportSemiringAppIssue e
    toTopVar e
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if isSameExpr (← getAddFn').appArg! i then return some (.add (← go a) (← go b)) else asTopVar e
  | HMul.hMul _ _ _ i a b =>
    if isSameExpr (← getMulFn').appArg! i then return some (.mul (← go a) (← go b)) else asTopVar e
  | HPow.hPow _ _ _ i a b =>
    let some k := Sym.getNatValue? b |>.run | return none
    if isSameExpr (← getPowFn').appArg! i then return some (.pow (← go a) k) else asTopVar e
  | NatCast.natCast _ i a =>
    if isSameExpr (← getNatCastFn').appArg! i then
      let some k := Sym.getNatValue? a |>.run | toTopVar e
      return some (.num k)
    else
      asTopVar e
  | OfNat.ofNat _ n _ =>
    let .lit (.natVal k) := n | asTopVar e
    return some (.num k)
  | _ => toTopVar e

end SemiringReify

end Lean.Meta.Sym.Arith
