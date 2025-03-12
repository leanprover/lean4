/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Alex Keizer, Siddharth Bhat
-/
prelude
import Lean.Meta.Tactic.AC.Main
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean Meta

/-! ### Expr helpers -/
section Expr

namespace BitVec

def mkType (w : Expr) : Expr := mkApp (.const ``BitVec []) w

def mkInstMul (w : Expr) : Expr := mkApp (.const ``BitVec.instMul []) w

def mkInstHMul (w : Expr) : Expr :=
  mkApp2 (mkConst ``instHMul [levelZero]) (BitVec.mkType w) (mkInstMul w)

end BitVec

/-- Construct a literal of type `BitVec w`, with value `n` -/
def mkBitVecLit (w : Expr) (n : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat []) w (mkNatLit n)

end Expr

/-! ### Types -/

abbrev VarIndex := Nat



/-- Bitvector operations that we perform AC canonicalization on. -/
inductive Op
  | mul (w : Expr)
deriving BEq, Repr

namespace Op

/-- Given an expression of an (unapplied) operation, return the decoded `Op`.

Return `none` if the expression is not a recognized operation. -/
def ofExpr? (e : Expr) : Option Op :=
  match_expr e with
  | HMul.hMul bv _bv _bv _inst =>
    let_expr BitVec w := bv | none
    some (.mul w)
  | _ => none

/-- Given an *application* of a recognized binary operation (to two arguments),
return the decoded `Op`.

Return `none` if the expression is not an application of a recognized operation.
-/
def ofApp2? : Expr → Option Op
  | mkApp2 op _x _y => ofExpr? op
  | _ => none

def toExpr : Op → Expr
  | .mul w =>
    let bv := BitVec.mkType w
    let inst := BitVec.mkInstHMul w
    mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) bv bv bv inst

/-- The identity / neutral element of given operation -/
def neutralElement : Op → Expr
  | .mul w => mkBitVecLit w 1

/-- Parse `op'` using `ofExpr?` and return true if the resulting operation is
of the same kind as `op` (i.e., both are multiplications).
Returns false if `op'` fails to parse.

Note that the width of the operation is *not* compared.
 -/
def isSameKind (op : Op) (op' : Expr) : Bool := Id.run do
  let some op' := ofExpr? op' | false
  match op, op' with
  | .mul _, .mul _ => true

instance : ToMessageData Op where
  toMessageData op := m!"{toExpr op}"

end Op

structure VarState where
  /-- The associative and commutative operator we are currently canonicalizing with respect to. -/
  op : Op
  /-- Map from atomic expressions to an index. -/
  exprToVarIndex : Std.HashMap Expr VarIndex := {}
  /-- Inverse of `exprToVarIndex`, which maps a `VarIndex` to the expression it represents. -/
  varToExpr : Array Expr := #[]

/-!
We don't verify the state manipulations, but if we would, these are the invariants:
```
structure LegalVarState extends VarState where
  /-- `varToExpr` and `exprToVarIndex` have the same number of elements. -/
  h_size  : varToExpr.size = exprToVarIndex.size
  /-- `exprToVarIndex` is the inverse of `varToExpr`. -/
  h_elems : ∀ h_lt : i < varToExpr.size, exprToVarIndex[varToExpr[i]]? = some i
```
-/

/-- A representation of an expression as a map from variable index to the number
of occurences of the expression represented by that variable.

See `CoefficientsMap.toExpr` for the explicit conversion. -/
abbrev CoefficientsMap := Std.HashMap VarIndex Nat

/-! ### VarState monadic boilerplate  -/

abbrev VarStateM  := StateT VarState MetaM

def VarStateM.run' (x : VarStateM α) (s : VarState) : MetaM α :=
  StateT.run' x s

/-! ### Implementation -/

/-- Return the unique variable index for an expression, or `none` if the expression
is a neutral element (see `isNeutral`).

Modifies the monadic state to add a new mapping, if needed. -/
def VarStateM.exprToVar (e : Expr) : VarStateM VarIndex := do
  match ← getIndex e with
  | some idx => return idx
  | none =>
    modifyGet fun s =>
      let nextIndex := s.exprToVarIndex.size
      (nextIndex, { s with
        exprToVarIndex := s.exprToVarIndex.insert e nextIndex
        varToExpr := s.varToExpr.push e
      })
where
  /-- Lookup the index of expression `e` in the monadic state. -/
  getIndex (e : Expr) : VarStateM (Option VarIndex) := do
    return (← get).exprToVarIndex[e]?

/-- Return the expression that is represented by a specific variable index. -/
def VarStateM.varToExpr (idx : VarIndex) : VarStateM Expr := do
  let varToExpr := (← get).varToExpr
  if h : idx < varToExpr.size then
    return varToExpr[idx]
  else
    throwError "internal error (this is a bug!): index {idx} out of range, \
      the current state only has {varToExpr.size} variables:\n\n{varToExpr}"


/-- Given a binary, associative and commutative operation `op`,
decompose expression `e` into its variable coefficients.

For example `a ⊕ b ⊕ (a ⊕ c)` will give the coefficients:
```
a => 2
b => 1
c => 1
```

Any compound expression which is not an application of the given `op` will be
abstracted away and treated as a variable (see `VarStateM.exprToVar`).

Note that the output is guaranteed to map at least one variable to a non-zero
coefficient, *unless* the input expression only contains applications of neutral
elements (e.g., `0 + (0 + 0)`), in which case the returned coefficients map will
be empty.
-/
def VarStateM.computeCoefficients (op : Op) (e : Expr) : VarStateM CoefficientsMap :=
  go {} e
where
  incrVar (coeff : CoefficientsMap) (e : Expr) : VarStateM CoefficientsMap := do
    let idx ← exprToVar e
    return coeff.alter idx (fun c => some <| (c.getD 0) + 1)
  go (coeff : CoefficientsMap) : Expr → VarStateM CoefficientsMap
    | e@(AC.bin op' x y) => do
        if op.isSameKind op' then
          let coeff ← go coeff x
          let coeff ← go coeff y
          return coeff
        else
          trace[Meta.AC] "Found binary operation '{op'} {x} {y}', expected '{op}'.\
            Treating as atom."
          incrVar coeff e
    | e => incrVar coeff e

structure SharedCoefficients where
  common : CoefficientsMap := {}
  x : CoefficientsMap
  y : CoefficientsMap

/-- Given two sets of coefficients `x` and `y` (computed with the same variable
mapping), extract the shared coefficients, such that `x` (resp. `y`) is the sum of
coefficients in `common` and `x` (resp `y`) of the result.

That is, if `{ common, x', y' } ← SharedCoeffients.compute x y`, then
  `x[idx] = common[idx] + x'[idx]` and
  `y[idx] = common[idx] + y'[idx]`
for all valid variable indices `idx`.
-/
def SharedCoefficients.compute (x y : CoefficientsMap) : VarStateM SharedCoefficients := do
  let swappedXy := x.size > y.size
  let (x, y) := if swappedXy then (y, x) else (x, y)
  -- This is O(|x|) = O(min(|x|, |y|)) as we sort by size above.
  let common : CoefficientsMap := x.fold (init := {}) fun common idx xCnt =>
    match y[idx]? with
    | some yCnt => common.insert idx <| min xCnt yCnt
    | _ => common

  let x : CoefficientsMap := common.fold (init := x) fun x idx commonCnt =>
    x.modify idx (fun cnt => cnt - commonCnt)

  let y : CoefficientsMap := common.fold (init := y) fun y idx commonCnt =>
    y.modify idx (fun cnt => cnt - commonCnt)

  let (x, y) := if swappedXy then (y, x) else (x, y)
  return { x, y, common }

/-- Compute the canonical expression for a given set of coefficients.
Returns `none` if all coefficients are zero.
-/
def CoefficientsMap.toExpr (coeff : CoefficientsMap) (op : Op) : VarStateM (Option Expr) := do
  -- Note: we iterate over a sorted array of indices
  -- to ensure a canonical order of variables in the returned expression.
  -- This is O(|coeff| log |coeff|).
  let coeffArr := coeff.toArray.qsort (·.fst < ·.fst)
  let mut acc : Option Expr := none
  for (var, coeff) in coeffArr do
    let expr := (← get).varToExpr[var]!
    for _ in [0:coeff] do
      acc := match acc with
        | none => expr
        | some acc => some <| mkApp2 op.toExpr acc expr
  return acc

open VarStateM Lean.Meta Lean.Elab Term


/--
Given two expressions `x, y` which are equal up to associativity and commutativity,
construct and return a proof of `x = y`.

Uses `ac_rfl` internally to contruct said proof. -/
def proveEqualityByAC (x y : Expr) : MetaM Expr := do
  let expectedType ← mkEq x y
  let proof ← mkFreshExprMVar expectedType
  AC.rewriteUnnormalizedRefl proof.mvarId! -- invoke `ac_rfl`
  instantiateMVars proof


/--
Given an expression `P lhs rhs`, where `lhs, rhs : ty` and `P : $ty → $ty → _`,
canonicalize top-level applications of a recognized associative and commutative
operation on both the `lhs` and the `rhs` such that the final expression is:
  `P ($common ⊕ $lhs') ($common ⊕ $rhs')`
That is, in a way that exposes terms that are shared between the lhs and rhs.

For example, `x₁ * (y₁ * z) == x₂ * (y₂ * z)` is normalized to
`z * (x₁ * y₁) == z * (x₂ * y₂)`, pulling the shared variable `z` to the front on
both sides.

Note that if both lhs and rhs are applications of a *different* operation, we
canonicalize according to the *left* operation, meaning we treat the entire rhs
as an atom. This is still useful, as it will pull out an occurence of the rhs
in the lhs (if present) to the front (such an occurence would be the common
expression). For example `x + y + ((x * y) + x) = x * y` will be canonicalized
to `(x * y) + ... = x * y`.

See `Op.fromExpr?` to see which operations are recognized.
Other operations are ignored, even if they are associative and commutative.
-/
def canonicalizeWithSharing (P : Expr) (lhs rhs : Expr) : SimpM Simp.Step := do
  withTraceNode (collapsed := false) `Meta.AC (fun _ => pure m!"canonicalizeWithSharing") <| do
  trace[Meta.AC] "Canonicalizing: {indentExpr <| mkApp2 P lhs rhs}"

  let some op := Op.ofApp2? lhs |
    trace[Meta.AC] "Failed to recognize operation: {indentExpr lhs}"
    return .continue
  let some op' := Op.ofApp2? rhs |
    trace[Meta.AC] "Failed to recognize operation: {indentExpr rhs}"
    return .continue

  -- Ignore cases where LHS and RHS ops are different.
  if op != op' then
    trace[Meta.AC] "Operations mismatch:\
      the left-hand-side has operation {op}
        {indentExpr lhs}
      but the right-hand-side has operation {op'}
        {indentExpr rhs}"
    return .continue

  trace[Meta.AC] "Canonicalizing with respect to operation: '{op}' K"

  VarStateM.run' (s:= { op }) do
    let lCoeff ← computeCoefficients op lhs
    let rCoeff ← computeCoefficients op rhs

    let ⟨commonCoeff, lCoeff, rCoeff⟩ ← SharedCoefficients.compute lCoeff rCoeff
    let commonExpr? : Option Expr ← commonCoeff.toExpr op
    let lNew? : Option Expr ← lCoeff.toExpr op
    let rNew? : Option Expr ← rCoeff.toExpr op

    -- Since `lCoeff_{old} = commonCoeff + lCoeff_{new}`, and all coefficients
    -- of `lCoeff_{old}` are zero iff `lExpr` contains only neutral elements,
    -- we default to `lNew` being some canonical neutral element if both
    -- `commonExpr?` and `lNew?` are `none`.
    let lNew := Option.merge (mkApp2 op.toExpr) commonExpr? lNew? |>.getD op.neutralElement
    let rNew := Option.merge (mkApp2 op.toExpr) commonExpr? rNew? |>.getD op.neutralElement

    let oldExpr := mkApp2 P lhs rhs
    let expr := mkApp2 P lNew rNew
    check oldExpr
    check expr
    let proof ← proveEqualityByAC oldExpr expr

    return Simp.Step.continue <| some {
      expr := expr
      proof? := some proof
    }

def bvAcNfpost : Simp.Simproc := fun e => do
  match_expr e with
  | BEq.beq ty inst lhs rhs =>
      trace[Meta.AC] "bv_ac_nf {checkEmoji} found `BEq.beq`."
      let uLvl ← getDecLevel ty
      let P := mkApp2 (.const ``BEq.beq [uLvl]) ty inst
      let out ← canonicalizeWithSharing P lhs rhs
      return out
  | Eq ty lhs rhs =>
      trace[Meta.AC] "bv_ac_nf {checkEmoji} found `Eq`."
      let uLvl ← getLevel ty
      let P := mkApp (.const ``Eq [uLvl]) ty
      let out ← canonicalizeWithSharing P lhs rhs
      return out
  | _ =>
    return .continue

/-! ## Tactic Boilerplate -/

open Tactic

def bvAcNfTarget (mvarId : MVarId)
    (maxSteps : Nat := Lean.Meta.Simp.defaultMaxSteps) : MetaM MVarId := do
  let simpCtx ← Simp.mkContext
      (simpTheorems  := {})
      (congrTheorems := (← getSimpCongrTheorems))
      (config        := { Simp.neutralConfig with maxSteps})
  let tgt ← instantiateMVars (← mvarId.getType)
  let (res, _) ← Simp.main tgt simpCtx (methods := { post := bvAcNfpost })
  applySimpResultToTarget mvarId tgt res


def bvAcNfHypMeta (goal : MVarId) (fvarId : FVarId)
    (maxSteps : Nat := Lean.Meta.Simp.defaultMaxSteps) : MetaM (Option MVarId) := do
  goal.withContext do
    let simpCtx ← Simp.mkContext
      (simpTheorems  := {})
      (congrTheorems := (← getSimpCongrTheorems))
      (config        := { Simp.neutralConfig with maxSteps})
    let tgt ← instantiateMVars (← fvarId.getType)
    let (res, _) ← Simp.main tgt simpCtx (methods := { post := bvAcNfpost })
    return (← applySimpResultToLocalDecl goal fvarId res false).map (·.snd)

/--
Normalize the tactic target up to associativity and commutativity of bitvector
multiplication, in a way that exposes common terms among both sides of an equality.

This is similar to the `ac_nf` tactic, except that it is specialized to bitvector
multiplication, and it differs in how the canonical form of the left-hand-side of
an equality can depend on the right-hand-side, in particular, to expose shared terms.

For example, `x₁ * (y₁ * z) = x₂ * (y₂ * z)` is normalized to
`z * (x₁ * y₁) = z * (x₂ * y₂)`, pulling the shared variable `z` to the front on
both sides.
-/
def bvAcNfTargetTactic : TacticM Unit := do
  liftMetaTactic1 fun goal => bvAcNfTarget goal

/--
Normalize an hypothesis up to associativity and commutativity of bitvector
multiplication, in a way that exposes common terms among both sides of an equality.

This is similar to the `ac_nf` tactic, except that it is specialized to bitvector
multiplication, and it differs in how the canonical form of the left-hand-side of
an equality can depend on the right-hand-side, in particular, to expose shared terms.

For example, `x₁ * (y₁ * z) = x₂ * (y₂ * z)` is normalized to
`z * (x₁ * y₁) = z * (x₂ * y₂)`, pulling the shared variable `z` to the front on
both sides.
-/
def bvAcNfHypTactic (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun goal => bvAcNfHypMeta goal fvarId

def bvAcNormalizePass (maxSteps : Nat) : Pass where
  name := `bv_ac_nf
  run' goal := do
    let mut newGoal := goal
    for hyp in (← goal.getNondepPropHyps) do
      if let .some nextGoal ← bvAcNfHypMeta newGoal hyp maxSteps then
        newGoal := nextGoal
    return newGoal

end Frontend.Normalize
