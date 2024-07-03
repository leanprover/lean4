/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.InferType

/-!
This module contains the logic that packs the motives and FArgs of multiple functions into one,
to allow structural mutual recursion where the number of functions is not exactly the same
as the number of inductive data types in the mutual inductive group.

The private helper functions related to `PProd` here should at some point be moved to their own
module, so that they can be used elsewhere (e.g. `FunInd`), and possibly unified with the similar
constructions for well-founded recursion (see `ArgsPacker` module).
-/

namespace Lean.Elab.Structural
open Meta

private def mkPUnit : Level → Expr
  | .zero => .const ``True []
  | lvl   => .const ``PUnit [lvl]

private def mkPProd (e1 e2 : Expr) : MetaM Expr := do
  let lvl1 ← getLevel e1
  let lvl2 ← getLevel e2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp2 (.const `And []) e1 e2
  else
    return mkApp2 (.const ``PProd [lvl1, lvl2]) e1 e2

private def mkNProd (lvl : Level) (es : Array Expr) : MetaM Expr :=
  es.foldrM (init := mkPUnit lvl) mkPProd

private def mkPUnitMk : Level → Expr
  | .zero => .const ``True.intro []
  | lvl   => .const ``PUnit.unit [lvl]

private def mkPProdMk (e1 e2 : Expr) : MetaM Expr := do
  let t1 ← inferType e1
  let t2 ← inferType e2
  let lvl1 ← getLevel t1
  let lvl2 ← getLevel t2
  if lvl1 matches .zero && lvl2 matches .zero then
    return mkApp4 (.const ``And.intro []) t1 t2 e1 e2
  else
    return mkApp4 (.const ``PProd.mk [lvl1, lvl2]) t1 t2 e1 e2

private def mkNProdMk (lvl : Level) (es : Array Expr) : MetaM Expr :=
  es.foldrM (init := mkPUnitMk lvl) mkPProdMk

/-- `PProd.fst` or `And.left` (as projections) -/
private def mkPProdFst (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd _ _ => return .proj ``PProd 0 e
  | And _ _ =>   return .proj ``And 0 e
  | _ => throwError "Cannot project .1 out of{indentExpr e}\nof type{indentExpr t}"

/-- `PProd.snd` or `And.right` (as projections) -/
private def mkPProdSnd (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd _ _ => return .proj ``PProd 1 e
  | And _ _ =>   return .proj ``And 1 e
  | _ => throwError "Cannot project .2 out of{indentExpr e}\nof type{indentExpr t}"

/-- Given a proof of `P₁ ∧ … ∧ Pᵢ ∧ … ∧ Pₙ ∧ True`, return the proof of `Pᵢ` -/
def mkPProdProjN (i : Nat) (e : Expr) : MetaM Expr := do
  let mut value := e
  for _ in [:i] do
      value ← mkPProdSnd value
  value ← mkPProdFst value
  return value

/--
Combines motives from different functions that recurse on the same parameter type into a single
function returning a `PProd` type.

For example
```
packMotives (Nat → Sort u) #[(fun (n : Nat) => Nat), (fun (n : Nat) => Fin n -> Fin n )]
```
will return
```
fun (n : Nat) (PProd Nat (Fin n → Fin n))
```

It is the identity if `motives.size = 1`.

It returns a dummy motive `(xs : ) → PUnit` or `(xs : … ) → True` if no motive is given.
(this is the reason we need the expected type in the `motiveType` parameter).

-/
def packMotives (motiveType : Expr) (motives : Array Expr) : MetaM Expr := do
  if motives.size = 1 then
    return motives[0]!
  trace[Elab.definition.structural] "packing Motives\nexpected: {motiveType}\nmotives: {motives}"
  forallTelescope motiveType fun xs sort => do
    unless sort.isSort do
      throwError "packMotives: Unexpected motiveType {motiveType}"
    -- NB: Use beta, not instantiateLambda; when constructing the belowDict below
    -- we pass `C`, a plain FVar, here
    let motives := motives.map (·.beta xs)
    let packedMotives ← mkNProd sort.sortLevel! motives
    mkLambdaFVars xs packedMotives

/--
Combines the F-args from different functions that recurse on the same parameter type into a single
function returning a `PProd` value. See `packMotives`

It is the identity if `motives.size = 1`.
-/
def packFArgs (FArgType : Expr) (FArgs : Array Expr) : MetaM Expr := do
  if FArgs.size = 1 then
    return FArgs[0]!
  forallTelescope FArgType fun xs body => do
    let lvl ← getLevel body
    let FArgs := FArgs.map (·.beta xs)
    let packedFArgs ← mkNProdMk lvl FArgs
    mkLambdaFVars xs packedFArgs


end Lean.Elab.Structural
