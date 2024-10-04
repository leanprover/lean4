/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.InferType

/-!
This module provides functions to pack and unpack values using nested `PProd` or `And`,
as used in the `.below` construction, in the `.brecOn` construction for mutual recursion and
and the `mutual_induct` construction.

It uses `And` (equivalent to `PProd.{0}` when possible).

The nesting is `t₁ ×' (t₂ ×' t₃)`, not `t₁ ×' (t₂ ×' (t₃ ×' PUnit))`. This is more readable,
slightly shorter, and means that the packing is the identity if `n=1`, which we rely on in some
places. It comes at the expense that hat projection needs to know `n`.

Packing an empty list uses `True` or `PUnit` depending on the given `lvl`.

Also see `Lean.Meta.ArgsPacker` for a similar module for `PSigma` and `PSum`, used by well-founded recursion.
-/


namespace Lean.Meta

/-- Given types `t₁` and `t₂`, produces `t₁ ×' t₂` (or `t₁ ∧ t₂` if the universes allow) -/
def mkPProd (e1 e2 : Expr) : MetaM Expr := do
  let lvl1 ← getLevel e1
  let lvl2 ← getLevel e2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp2 (.const `And []) e1 e2
  else
    return mkApp2 (.const ``PProd [lvl1, lvl2]) e1 e2

/-- Given values of typs `t₁` and `t₂`, produces value of type `t₁ ×' t₂` (or `t₁ ∧ t₂` if the universes allow) -/
def mkPProdMk (e1 e2 : Expr) : MetaM Expr := do
  let t1 ← inferType e1
  let t2 ← inferType e2
  let lvl1 ← getLevel t1
  let lvl2 ← getLevel t2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp4 (.const ``And.intro []) t1 t2 e1 e2
  else
    return mkApp4 (.const ``PProd.mk [lvl1, lvl2]) t1 t2 e1 e2

/-- `PProd.fst` or `And.left` (using `.proj`) -/
def mkPProdFst (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd _ _ => return .proj ``PProd 0 e
  | And _ _ => return .proj ``And 0 e
  | _ => panic! "mkPProdFst: cannot handle{indentExpr e}\nof type{indentExpr t}"

/-- `PProd.snd` or `And.right` (using `.proj`) -/
def mkPProdSnd (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd _ _ => return .proj ``PProd 1 e
  | And _ _ => return .proj ``And 1 e
  | _ => panic! "mkPProdSnd: cannot handle{indentExpr e}\nof type{indentExpr t}"



namespace PProdN

/-- Given types `tᵢ`, produces `t₁ ×' t₂ ×' t₃` -/
def pack (lvl : Level) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    if lvl matches .zero then return .const ``True []
                         else return .const ``PUnit [lvl]
  let xBack := xs.back
  xs.pop.foldrM mkPProd xBack

/-- Given values `xᵢ` of type `tᵢ`, produces value of type `t₁ ×' t₂ ×' t₃` -/
def mk (lvl : Level) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    if lvl matches .zero then return .const ``True.intro []
                         else return .const ``PUnit.unit [lvl]
  let xBack := xs.back
  xs.pop.foldrM mkPProdMk xBack

/-- Given a value of type `t₁ ×' … ×' tᵢ ×' … ×' tₙ`, return a value of type `tᵢ` -/
def proj (n i : Nat) (e : Expr) : MetaM Expr := do
  let mut value := e
  for _ in [:i] do
      value ← mkPProdSnd value
  if i+1 < n then
    mkPProdFst value
  else
    pure value



/--
Packs multiple type-forming lambda expressions taking the same parameters using `PProd`.

The parameter `type` is the common type of the these expressions

For example
```
packLambdas (Nat → Sort u) #[(fun (n : Nat) => Nat), (fun (n : Nat) => Fin n -> Fin n )]
```
will return
```
fun (n : Nat) => (Nat ×' (Fin n → Fin n))
```

It is the identity if `es.size = 1`.

It returns a dummy motive `(xs : ) → PUnit` or `(xs : … ) → True` if no expressions are given.
(this is the reason we need the expected type in the `type` parameter).

-/
def packLambdas (type : Expr) (es : Array Expr) : MetaM Expr := do
  if h : es.size = 1 then
    return es[0]
  forallTelescope type fun xs sort => do
    assert! sort.isSort
    -- NB: Use beta, not instantiateLambda; when constructing the belowDict below
    -- we pass `C`, a plain FVar, here
    let es' := es.map (·.beta xs)
    let packed ← PProdN.pack sort.sortLevel! es'
    mkLambdaFVars xs packed

/--
The value analogue to `PProdN.packLambdas`.

It is the identity if `es.size = 1`.
-/
def mkLambdas (type : Expr) (es : Array Expr) : MetaM Expr := do
  if h : es.size = 1 then
    return es[0]
  forallTelescope type fun xs body => do
    let lvl ← getLevel body
    let es' := es.map (·.beta xs)
    let packed ← PProdN.mk lvl es'
    mkLambdaFVars xs packed


end PProdN

end Lean.Meta
