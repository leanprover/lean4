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
import Lean.Meta.PProdN

namespace Lean
open Meta

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
-/
private def buildBelowMinorPremise (rlvl : Level) (motives : Array Expr) (minorType : Expr) : MetaM Expr :=
  forallTelescope minorType fun minor_args _ => do go #[] minor_args.toList
where
  go (prods : Array Expr) : List Expr → MetaM Expr
  | [] => PProdN.pack rlvl prods
  | arg::args => do
    let argType ← inferType arg
    forallTelescope argType fun arg_args arg_type => do
      if motives.contains arg_type.getAppFn then
        let name ← arg.fvarId!.getUserName
        let type' ← forallTelescope argType fun args _ => mkForallFVars args (.sort rlvl)
        withLocalDeclD name type' fun arg' => do
          let e' ← mkForallFVars arg_args <| ← mkPProd arg_type (mkAppN arg' arg_args)
          mkLambdaFVars #[arg'] (← go (prods.push e') args)
      else
        mkLambdaFVars #[arg] (← go prods args)

/--
Constructs the `.below` definition for a inductive predicate.

For example for the `List` type, it constructs,
```
@[reducible] protected def List.below.{u_1, u} : {α : Type u} →
  {motive : List α → Sort u_1} → List α → Sort (max 1 u_1) :=
fun {α} {motive} t =>
  List.rec PUnit (fun head tail tail_ih => PProd (PProd (motive tail) tail_ih) PUnit) t
```
-/
private def mkBelowFromRec (recName : Name) (reflexive : Bool) (nParams : Nat)
  (belowName : Name) : MetaM Unit := do
  -- The construction follows the type of `ind.rec`
  let .recInfo recVal ← getConstInfo recName
    | throwError "{recName} not a .recInfo"
  let lvl::lvls := recVal.levelParams.map (Level.param ·)
    | throwError "recursor {recName} has no levelParams"

  let decl ← forallTelescope recVal.type fun refArgs _ => do
    assert! refArgs.size > nParams + recVal.numMotives + recVal.numMinors
    let params  : Array Expr := refArgs[:nParams]
    let motives : Array Expr := refArgs[nParams:nParams + recVal.numMotives]
    let minors  : Array Expr := refArgs[nParams + recVal.numMotives:nParams + recVal.numMotives + recVal.numMinors]
    let indices : Array Expr := refArgs[nParams + recVal.numMotives + recVal.numMinors:refArgs.size - 1]
    let major   : Expr       := refArgs[refArgs.size - 1]!

    -- universe parameter of the type fomer.
    -- same as `typeFormerTypeLevel indVal.type`, but we want to infer it from the
    -- type of the recursor, to be more robust when facing nested induction
    let majorTypeType ← inferType (← inferType major)
    let .some ilvl ← typeFormerTypeLevel majorTypeType
      | throwError "type of type of major premise {major} not a type former"

    -- universe level of the resultant type
    let rlvl : Level :=
      if reflexive then
        mkLevelMax ilvl lvl
      else
        mkLevelMax 1 lvl

    let mut val := .const recName (rlvl.succ :: lvls)
    -- add parameters
    val := mkAppN val params
    -- add type formers
    for motive in motives do
      let arg ← forallTelescope (← inferType motive) fun targs _ =>
        mkLambdaFVars targs (.sort rlvl)
      val := .app val arg
    -- add minor premises
    for minor in minors do
      let arg ← buildBelowMinorPremise rlvl motives (← inferType minor)
      val := .app val arg
    -- add indices and major premise
    val := mkAppN val indices
    val := mkApp val major

    -- All parameters of `.rec` besides the `minors` become parameters of `.below`
    let below_params := params ++ motives ++ indices ++ #[major]
    let type ← mkForallFVars below_params (.sort rlvl)
    val ← mkLambdaFVars below_params val

    mkDefinitionValInferrringUnsafe belowName recVal.levelParams type val .abbrev

  addDecl (.defnDecl decl)
  setReducibleAttribute decl.name
  modifyEnv fun env => markAuxRecursor env decl.name
  modifyEnv fun env => addProtected env decl.name

def mkBelow (indName : Name) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo indName | return
  unless indVal.isRec do return
  if ← isPropFormerType indVal.type then return

  let recName := mkRecName indName
  let belowName := mkBelowName indName
  mkBelowFromRec recName indVal.isReflexive indVal.numParams belowName

  -- If this is the first inductive in a mutual group with nested inductives,
  -- generate the constructions for the nested inductives now
  if indVal.all[0]! = indName then
    for i in [:indVal.numNested] do
      let recName := recName.appendIndexAfter (i + 1)
      let belowName := belowName.appendIndexAfter (i + 1)
      mkBelowFromRec recName indVal.isReflexive indVal.numParams belowName

/--
If `minorType` is the type of a minor premies of a recursor, such as
```
  (cons : (head : α) → (tail : List α) → (tail_hs : motive tail) → motive (head :: tail))
```
of `List.rec`, constructs the corresponding argument to `List.rec` in the construction
of `.brecOn` definition; in this case
```
fun head tail tail_ih =>
  ⟨F_1 (head :: tail) ⟨tail_ih, PUnit.unit⟩, ⟨tail_ih, PUnit.unit⟩⟩
```
of type
```
(head : α) → (tail : List α) →
  PProd (motive tail) (List.below tail) →
  PProd (motive (head :: tail)) (PProd (PProd (motive tail) (List.below tail)) PUnit)
```
-/
private def buildBRecOnMinorPremise (rlvl : Level) (motives : Array Expr)
    (belows : Array Expr) (fs : Array Expr) (minorType : Expr) : MetaM Expr :=
  forallTelescope minorType fun minor_args minor_type => do
    let rec go (prods : Array Expr) : List Expr → MetaM Expr
      | [] => minor_type.withApp fun minor_type_fn minor_type_args => do
          let b ← PProdN.mk rlvl prods
          let .some idx := motives.idxOf? minor_type_fn
            | throwError m!"Did not find {minor_type} in {motives}"
          mkPProdMk (mkAppN fs[idx]! (minor_type_args.push b)) b
      | arg::args => do
        let argType ← inferType arg
        forallTelescope argType fun arg_args arg_type => do
          arg_type.withApp fun arg_type_fn arg_type_args => do
            if let .some idx := motives.idxOf? arg_type_fn then
              let name ← arg.fvarId!.getUserName
              let type' ← mkForallFVars arg_args
                (← mkPProd arg_type (mkAppN belows[idx]! arg_type_args) )
              withLocalDeclD name type' fun arg' => do
                mkLambdaFVars #[arg'] (← go (prods.push arg') args)
            else
              mkLambdaFVars #[arg] (← go prods args)
    go #[] minor_args.toList

/--
Constructs the `.brecOn` definition for a inductive predicate.

For example for the `List` type, it constructs,
```
@[reducible] protected def List.brecOn.{u_1, u} : {α : Type u} → {motive : List α → Sort u_1} →
  (t : List α) → ((t : List α) → List.below t → motive t) → motive t :=
fun {α} {motive} t (F_1 : (t : List α) → List.below t → motive t) => (
  @List.rec α (fun t => PProd (motive t) (@List.below α motive t))
    ⟨F_1 [] PUnit.unit, PUnit.unit⟩
    (fun head tail tail_ih => ⟨F_1 (head :: tail) ⟨tail_ih, PUnit.unit⟩, ⟨tail_ih, PUnit.unit⟩⟩)
    t
  ).1
```
-/
private def mkBRecOnFromRec (recName : Name) (reflexive : Bool) (nParams : Nat)
    (all : Array Name) (brecOnName : Name) : MetaM Unit := do
  let .recInfo recVal ← getConstInfo recName | return
  let lvl::lvls := recVal.levelParams.map (Level.param ·)
    | throwError "recursor {recName} has no levelParams"
  -- universe parameter names of brecOn
  let blps := recVal.levelParams

  let decl ← forallTelescope recVal.type fun refArgs refBody => do
    assert! refArgs.size > nParams + recVal.numMotives + recVal.numMinors
    let params  : Array Expr := refArgs[:nParams]
    let motives : Array Expr := refArgs[nParams:nParams + recVal.numMotives]
    let minors  : Array Expr := refArgs[nParams + recVal.numMotives:nParams + recVal.numMotives + recVal.numMinors]
    let indices : Array Expr := refArgs[nParams + recVal.numMotives + recVal.numMinors:refArgs.size - 1]
    let major   : Expr       := refArgs[refArgs.size - 1]!

    let some idx := motives.idxOf? refBody.getAppFn
      | throwError "result type of {recVal.type} is not one of {motives}"

    -- universe parameter of the type fomer.
    -- same as `typeFormerTypeLevel indVal.type`, but we want to infer it from the
    -- type of the recursor, to be more robust when facing nested induction
    let majorTypeType ← inferType (← inferType major)
    let .some ilvl ← typeFormerTypeLevel majorTypeType
      | throwError "type of type of major premise {major} not a type former"

    -- universe level of the resultant type
    let rlvl : Level :=
      if reflexive then
        mkLevelMax ilvl lvl
      else
        mkLevelMax 1 lvl

    -- One `below` for each motive, with the same motive parameters
    let blvls := lvl::lvls
    let belows := Array.ofFn (n := motives.size) fun ⟨i,_⟩ =>
      let belowName :=
        if let some n := all[i]? then
          mkBelowName n
        else
          .str all[0]! s!"below_{i-all.size + 1}"
      mkAppN (.const belowName blvls) (params ++ motives)

    -- create types of functionals (one for each motive)
    --   (F_1 : (t : List α) → (f : List.below t) → motive t)
    -- and bring parameters of that type into scope
    let mut fDecls : Array (Name × (Array Expr -> MetaM Expr)) := #[]
    for motive in motives, below in belows, i in [:motives.size] do
      let fType ← forallTelescope (← inferType motive) fun targs _ => do
        withLocalDeclD `f (mkAppN below targs) fun f =>
          mkForallFVars (targs.push f) (mkAppN motive targs)
      let fName := .mkSimple s!"F_{i + 1}"
      fDecls := fDecls.push (fName, fun _ => pure fType)
    withLocalDeclsD fDecls fun fs => do
      let mut val := .const recName (rlvl :: lvls)
      -- add parameters
      val := mkAppN val params
      -- add type formers
      for motive in motives, below in belows do
        -- example: (motive := fun t => PProd (motive t) (@List.below α motive t))
        let arg ← forallTelescope (← inferType motive) fun targs _ => do
          let cType := mkAppN motive targs
          let belowType := mkAppN below targs
          let arg ← mkPProd cType belowType
          mkLambdaFVars targs arg
        val := .app val arg
      -- add minor premises
      for minor in minors do
        let arg ← buildBRecOnMinorPremise rlvl motives belows fs (← inferType minor)
        val := .app val arg
      -- add indices and major premise
      val := mkAppN val indices
      val := mkApp val major
      -- project out first component
      val ← mkPProdFstM val

      -- All parameters of `.rec` besides the `minors` become parameters of `.bRecOn`, and the `fs`
      let below_params := params ++ motives ++ indices ++ #[major] ++ fs
      let type ← mkForallFVars below_params (mkAppN motives[idx]! (indices ++ #[major]))
      val ← mkLambdaFVars below_params val

      mkDefinitionValInferrringUnsafe brecOnName blps type val .abbrev

  addDecl (.defnDecl decl)
  setReducibleAttribute decl.name
  modifyEnv fun env => markAuxRecursor env decl.name
  modifyEnv fun env => addProtected env decl.name

def mkBRecOn (indName : Name) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo indName | return
  unless indVal.isRec do return
  if ← isPropFormerType indVal.type then return

  let recName := mkRecName indName
  let brecOnName := mkBRecOnName indName
  mkBRecOnFromRec recName indVal.isReflexive indVal.numParams indVal.all.toArray brecOnName

  -- If this is the first inductive in a mutual group with nested inductives,
  -- generate the constructions for the nested inductives now.
  if indVal.all[0]! = indName then
    for i in [:indVal.numNested] do
      let recName := recName.appendIndexAfter (i + 1)
      let brecOnName := brecOnName.appendIndexAfter (i + 1)
      mkBRecOnFromRec recName indVal.isReflexive indVal.numParams indVal.all.toArray brecOnName
