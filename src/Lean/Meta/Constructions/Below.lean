/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.InferType
import Lean.AuxRecursor
import Lean.AddDecl
import Lean.Meta.CompletionName

namespace Lean
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

/--
If `minorType` is the type of a minor premies of a recursor, such as
```
  (cons : (head : α) → (tail : List α) → (tail_hs : motive tail) → motive (head :: tail))
```
of `List.rec`, constructs the corresponding argument to `List.rec` in the construction
of `.below` definition; in this case
```
fun head tail tail_ih =>
  PProd (PProd (motive tail) tail_ih) PUnit
```
of type
```
α → List α → Sort (max 1 u_1) → Sort (max 1 u_1)
```
The parameter `typeFormers` are the `motive`s.
-/
private def buildMinorPremise (rlvl : Level) (typeFormers : Array Expr) (minorType : Expr) : MetaM Expr :=
  forallTelescope minorType fun minor_args _ => do go #[] minor_args.toList
where
  ibelow := rlvl matches .zero
  go (prods : Array Expr) : List Expr → MetaM Expr
  | [] => mkNProd rlvl prods
  | arg::args => do
    let argType ← inferType arg
    forallTelescope argType fun arg_args arg_type => do
      if typeFormers.contains arg_type.getAppFn then
        let name ← arg.fvarId!.getUserName
        let type' ← forallTelescope argType fun args _ => mkForallFVars args (.sort rlvl)
        withLocalDeclD name type' fun arg' => do
          let snd ← mkForallFVars arg_args (mkAppN arg' arg_args)
          let e' ← mkPProd argType snd
          mkLambdaFVars #[arg'] (← go (prods.push e') args)
      else
        mkLambdaFVars #[arg] (← go prods args)

/--
Constructs the `.below` or `.ibelow` definition for a inductive predicate.

For example for the `List` type, it constructs,
```
@[reducible] protected def List.below.{u_1, u} : {α : Type u} →
  {motive : List α → Sort u_1} → List α → Sort (max 1 u_1) :=
fun {α} {motive} t =>
  List.rec PUnit (fun head tail tail_ih => PProd (PProd (motive tail) tail_ih) PUnit) t
```
and
```
@[reducible] protected def List.ibelow.{u} : {α : Type u} →
  {motive : List α → Prop} → List α → Prop :=
fun {α} {motive} t =>
  List.rec True (fun head tail tail_ih => (motive tail ∧ tail_ih) ∧ True) t
```
-/
private def mkBelowOrIBelow (indName : Name) (ibelow : Bool) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo indName | return
  unless indVal.isRec do return
  if ← isPropFormerType indVal.type then return

  let recName := mkRecName indName
  -- The construction follows the type of `ind.rec`
  let .recInfo recVal ← getConstInfo recName
    | throwError "{recName} not a .recInfo"
  let lvl::lvls := recVal.levelParams.map (Level.param ·)
    | throwError "recursor {recName} has no levelParams"
  let lvlParam := recVal.levelParams.head!
  -- universe parameter names of ibelow/below
  let blvls :=
    -- For ibelow we instantiate the first universe parameter of `.rec` to `.zero`
    if ibelow then recVal.levelParams.tail!
              else recVal.levelParams
  let .some ilvl ← typeFormerTypeLevel indVal.type
    | throwError "type {indVal.type} of inductive {indVal.name} not a type former?"

  -- universe level of the resultant type
  let rlvl : Level :=
    if ibelow then
      0
    else if indVal.isReflexive then
      if let .max 1 lvl := ilvl then
        mkLevelMax' (.succ lvl) lvl
      else
        mkLevelMax' (.succ lvl) ilvl
    else
      mkLevelMax' 1 lvl

  let refType :=
    if ibelow then
      recVal.type.instantiateLevelParams [lvlParam] [0]
    else if indVal.isReflexive then
      recVal.type.instantiateLevelParams [lvlParam] [lvl.succ]
    else
      recVal.type

  let decl ← forallTelescope refType fun refArgs _ => do
    assert! refArgs.size == indVal.numParams + recVal.numMotives + recVal.numMinors + indVal.numIndices + 1
    let params      : Array Expr := refArgs[:indVal.numParams]
    let typeFormers : Array Expr := refArgs[indVal.numParams:indVal.numParams + recVal.numMotives]
    let minors      : Array Expr := refArgs[indVal.numParams + recVal.numMotives:indVal.numParams + recVal.numMotives + recVal.numMinors]
    let remaining   : Array Expr := refArgs[indVal.numParams + recVal.numMotives + recVal.numMinors:]

    let mut val := .const recName (rlvl.succ :: lvls)
    -- add parameters
    val := mkAppN val params
    -- add type formers
    for typeFormer in typeFormers do
      let arg ← forallTelescope (← inferType typeFormer) fun targs _ =>
        mkLambdaFVars targs (.sort rlvl)
      val := .app val arg
    -- add minor premises
    for minor in minors do
      let arg ← buildMinorPremise rlvl typeFormers (← inferType minor)
      val := .app val arg
    -- add indices and major premise
    val := mkAppN val remaining

    -- All paramaters of `.rec` besides the `minors` become parameters of `.below`
    let below_params := params ++ typeFormers ++ remaining
    let type ← mkForallFVars below_params (.sort rlvl)
    val ← mkLambdaFVars below_params val

    let name := if ibelow then mkIBelowName indName else mkBelowName indName
    mkDefinitionValInferrringUnsafe name blvls type val .abbrev

  addDecl (.defnDecl decl)
  setReducibleAttribute decl.name
  modifyEnv fun env => markAuxRecursor env decl.name
  modifyEnv fun env => addProtected env decl.name

def mkBelow (declName : Name) : MetaM Unit := mkBelowOrIBelow declName true
def mkIBelow (declName : Name) : MetaM Unit := mkBelowOrIBelow declName false
