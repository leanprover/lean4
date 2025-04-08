/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.InferType
import Lean.Meta.Transform

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
def mkPProdFst (t e : Expr) : Expr :=
  match_expr t with
  | PProd _ _ => .proj ``PProd 0 e
  | And _ _ => .proj ``And 0 e
  | _ => panic! s!"mkPProdFst: cannot handle {e}\nof type {t}"

/-- `PProd.fst` or `And.left` (using `.proj`), inferring the type of `e` -/
def mkPProdFstM (e : Expr) : MetaM Expr := do
  return mkPProdFst (← whnf (← inferType e)) e

private def mkTypeSnd (t : Expr) : Expr :=
  match_expr t with
  | PProd _ t => t
  | And _ t => t
  | _ => panic! s!"mkTypeSnd: cannot handle type {t}"

/-- `PProd.snd` or `And.right` (using `.proj`) -/
def mkPProdSnd (t e : Expr) : Expr :=
  match_expr t with
  | PProd _ _ => .proj ``PProd 1 e
  | And _ _ => .proj ``And 1 e
  | _ => panic! s!"mkPProdSnd: cannot handle {e}\nof type {t}"

/-- `PProd.snd` or `And.right` (using `.proj`), inferring the type of `e` -/
def mkPProdSndM (e : Expr) : MetaM Expr := do
  return mkPProdSnd (← whnf (← inferType e)) e

namespace PProdN

/--
Essentially a form of `foldrM1`. Underlies `pack` and `mk`, and is useful to construct proofs
that should follow the structure of `pack` and `mk` (e.g. admissibility proofs)
-/
def genMk {α : Type _} [Inhabited α] (mk : α → α → MetaM α) (xs : Array α) : MetaM α :=
  assert! !xs.isEmpty
  xs.pop.foldrM mk xs.back!

/-- Given types `tᵢ`, produces `t₁ ×' t₂ ×' t₃` -/
def pack (lvl : Level) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    if lvl matches .zero then return .const ``True []
                         else return .const ``PUnit [lvl]
  genMk mkPProd xs

/-- Given values `xᵢ` of type `tᵢ`, produces value of type `t₁ ×' t₂ ×' t₃` -/
def mk (lvl : Level) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    if lvl matches .zero then return .const ``True.intro []
                         else return .const ``PUnit.unit [lvl]
  genMk mkPProdMk xs

/-- Given a value `e` of type `t = t₁ ×' … ×' tᵢ ×' … ×' tₙ`, return a value of type `tᵢ` -/
def proj (n i : Nat) (t e : Expr) : Expr := Id.run <| do
  unless i < n do panic! "PProdN.proj: {i} not less than {n}"
  let mut t := t
  let mut value := e
  for _ in [:i] do
      value := mkPProdSnd t value
      t := mkTypeSnd t
  if i+1 < n then
    mkPProdFst t value
  else
    value

/-- Given a value `e` of type `t = t₁ ×' … ×' tᵢ ×' … ×' tₙ`, return the values of type `tᵢ` -/
def projs (n : Nat) (t e : Expr) : Array Expr :=
  Array.ofFn (n := n) fun i => PProdN.proj n i t e

/-- Given a value of type `t₁ ×' … ×' tᵢ ×' … ×' tₙ`, return a value of type `tᵢ` -/
def projM (n i : Nat) (e : Expr) : MetaM Expr := do
  let mut value := e
  for _ in [:i] do
      value ← mkPProdSndM value
  if i+1 < n then
    mkPProdFstM value
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


/--  Strips topplevel `PProd` and `And` projections -/
def stripProjs (e : Expr) : Expr :=
  match e with
  | .proj ``PProd _ e' => stripProjs e'
  | .proj ``And _ e' => stripProjs e'
  | e => e

/--
Reduces `⟨x,y⟩.1` redexes for `PProd` and `And`
-/
def reduceProjs (e : Expr) : CoreM Expr := do
  Core.transform e (post := fun e => do
    if e.isProj then
      if e.projExpr!.isAppOfArity ``PProd.mk 4 || e.projExpr!.isAppOfArity ``And.intro 2 then
        if e.projIdx! == 0 then
          return .continue e.projExpr!.appFn!.appArg!
        else
          return .continue e.projExpr!.appArg!
    return .continue
  )

end PProdN

end Lean.Meta
