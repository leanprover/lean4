/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.FinContra
import Lean.Meta.MatchUtil
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Util

namespace Lean.Meta.FinContra

/-
Given a term `e` of type `Fin` or `BitVec`, where the type has
`n` elements, and disequalities `h_i : a ≠ i`. `finContra`
constructs a proof of false of the following shape:
```
  Lean.FinContra.false_of_lt_zero (toNat e) <|
  Lean.FinContra.step (ofNe h_0) <|
  ...
  Lean.FinContra.step (ofNe h_{n-1}) <|
  bound e
```
Where
- `toNat` is `BitVec.toNat` or `Fin.val`.
- `ofNe` is `Lean.FinContra.BitVec.val_ne_of_ne` or `Fin.val_ne_of_ne`
- `bound` is `Lean.FinContra.lt_two_pow` or `Fin.isLt`
-/

/-- Abstract the `toNat`, `ofNe`, `bound` proof steps. -/
structure Methods where
  toNat : Expr → MetaM Expr
  ofNe  : Expr → MetaM Expr
  bound : Expr → MetaM Expr

/-- `BitVec` case -/
def bitVecMethods : Methods where
  toNat := fun e => mkAppM ``BitVec.toNat #[e]
  ofNe  := fun h => mkAppM ``Lean.FinContra.BitVec.val_ne_of_ne #[h]
  bound := fun e => mkAppM ``Lean.FinContra.BitVec.lt_two_pow #[e]

/-- `Fin` case -/
def finMethods : Methods where
  toNat := fun e => mkAppM ``Fin.val #[e]
  ofNe  := fun h => mkAppM ``Fin.val_ne_of_ne #[h]
  bound := fun e => mkAppM ``Fin.isLt #[e]

def getMethodsFor? (type : Expr) : MetaM (Option Methods) := do
  let type ← whnfD type
  if type.isAppOfArity ``BitVec 1 then
    return some bitVecMethods
  else if type.isAppOfArity ``Fin 1 then
    return some finMethods
  else
    return none

/-- If `type` is `Fin` or `BitVec` with a known dimension, returns the number of elements in the type. -/
def isFinType? (type : Expr) : MetaM (Option Nat) := do
  let type ← whnfD type
  if type.isAppOfArity ``BitVec 1 then
    let some n ← getNatValue? type.appArg! | return none
    return some (2 ^ n)
  else if type.isAppOfArity ``Fin 1 then
    getNatValue? type.appArg!
  else
    return none

/-- If `e` is a `BitVec` or `Fin` literal, returns its value as a natural number. -/
def isFinVal? (e : Expr) : MetaM (Option Nat) := do
  if let some ⟨_, n⟩ ← getBitVecValue? e then
    return some n.toNat
  else if let some ⟨_, n⟩ ← getFinValue? e then
    return some n.val
  else
    return none

/--
A disquality of of the form `expr ≠ val` if `inv = false` and `val ≠ expr` if `inv = true`
-/
structure NeFinValInfo where
  inv  : Bool
  expr : Expr
  val  : Nat

/--
Return disequality info if `prop` is a disequality of the form `e ≠ i` or `i ≠ e` where
`i` is a `Fin` or `BitVec` literal.
-/
def isNeFinVal? (prop : Expr) : MetaM (Option NeFinValInfo) := do
  let some (_, a, b) ← matchNe? prop | return none
  if let some n ← isFinVal? a then
    return some { inv := true, expr := b, val := n }
  else if let some n ← isFinVal? b then
    return some { inv := false, expr := a, val := n }
  else
    return none

/--
Constructs a proof of `False` using the `diseqs` where
`e : Fin n` or `e : BitVec m`, and `diseqs` is an array of size `n` or `2^m`,
and `diseqs[i]` contains a proof for `e ≠ i` where `i` a literal value.
-/
def mkProof (e : Expr) (diseqs : Array (Option Expr)) : MetaM Expr := do
  let type ← inferType e
  let some m ← getMethodsFor? type | unreachable!
  let mut proof ← m.bound e
  let n := diseqs.size
  for i in [:diseqs.size] do
    let some diseq := diseqs[n - i - 1]! | unreachable!
    let diseq ← m.ofNe diseq
    proof ← mkAppM ``Lean.FinContra.step #[diseq, proof]
  mkAppM ``Lean.FinContra.false_of_lt_zero #[proof]

/--
Try to construct a proof for `False` using disequalities on `e`
where `e : Fin n` (`numElems = n`) or `e : BitVec m` (`numElems = 2^m`).
The method tries to find disequalities `e ≠ i` in the local context.
-/
def cover? (e : Expr) (numElems : Nat) : MetaM (Option Expr) := do
  let mut found := 0
  let mut diseqs : Array (Option Expr) := Array.mkArray numElems none
  for localDecl in (← getLCtx) do
    if let some info ← isNeFinVal? localDecl.type then
      if e == info.expr then
      if h : info.val < diseqs.size then
      if diseqs[info.val].isNone then
        found := found + 1
        let proof ← if info.inv then
          mkAppM ``Ne.symm #[localDecl.toExpr]
        else
          pure localDecl.toExpr
        diseqs := diseqs.set! info.val (some proof)
  if found == numElems then
    return some (← mkProof e diseqs)
  else
    return none

/--
Return `true` if the given goal is contradicatory because
it contains a `Fin` or `BitVec` term and disequalities that eliminate all possibilities.
Example:
```
example (a : Fin 3) (h₁ : a ≠ 0) (h₂ : a ≠ 1) (h₃ : a ≠ 2) : False
```
-/
def finContra (mvarId : MVarId) : MetaM Bool := mvarId.withContext do
  mvarId.checkNotAssigned `finContradiction
  let mut visited : ExprSet := {}
  for localDecl in (← getLCtx) do
    if let some info ← isNeFinVal? localDecl.type then
      unless visited.contains info.expr do
        visited := visited.insert info.expr
        if let some size ← isFinType? (← inferType info.expr) then
          if let some proofOfFalse ← cover? info.expr size then
            let proof ← mkFalseElim (← mvarId.getType) proofOfFalse
            mvarId.assign proof
            return true
  return false

end Lean.Meta.FinContra
