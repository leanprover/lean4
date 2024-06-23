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

section PProd

/--!
Helpers to construct types and values of `PProd` and project out of them, set up to use `And`
instead of `PProd` if the universes allow. Maybe be extracted into a Utils module when useful
elsewhere.
-/

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

end PProd

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
private def buildBelowMinorPremise (rlvl : Level) (typeFormers : Array Expr) (minorType : Expr) : MetaM Expr :=
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
      let arg ← buildBelowMinorPremise rlvl typeFormers (← inferType minor)
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
The parameter `typeFormers` are the `motive`s.
-/
private def buildBRecOnMinorPremise (rlvl : Level) (typeFormers : Array Expr)
    (belows : Array Expr) (fs : Array Expr) (minorType : Expr) : MetaM Expr :=
  forallTelescope minorType fun minor_args minor_type => do
    let rec go (prods : Array Expr) : List Expr → MetaM Expr
      | [] => minor_type.withApp fun minor_type_fn minor_type_args => do
          let b ← mkNProdMk rlvl prods
          let .some ⟨idx, _⟩ := typeFormers.indexOf? minor_type_fn
            | throwError m!"Did not find {minor_type} in {typeFormers}"
          mkPProdMk (mkAppN fs[idx]! (minor_type_args.push b)) b
      | arg::args => do
        let argType ← inferType arg
        forallTelescope argType fun arg_args arg_type => do
          arg_type.withApp fun arg_type_fn arg_type_args => do
            if let .some idx := typeFormers.indexOf? arg_type_fn then
              let name ← arg.fvarId!.getUserName
              let type' ← mkForallFVars arg_args
                (← mkPProd arg_type (mkAppN belows[idx]! arg_type_args) )
              withLocalDeclD name type' fun arg' => do
                if arg_args.isEmpty then
                  mkLambdaFVars #[arg'] (← go (prods.push arg') args)
                else
                  let r := mkAppN arg' arg_args
                  let r₁ ← mkLambdaFVars arg_args (← mkPProdFst r)
                  let r₂ ← mkLambdaFVars arg_args (← mkPProdSnd r)
                  let r ← mkPProdMk r₁ r₂
                  mkLambdaFVars #[arg'] (← go (prods.push r) args)
            else
              mkLambdaFVars #[arg] (← go prods args)
    go #[] minor_args.toList

/--
Constructs the `.brecon` or `.binductionon` definition for a inductive predicate.

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
and
```
@[reducible] protected def List.binductionOn.{u} : ∀ {α : Type u} {motive : List α → Prop}
  (t : List α), (∀ (t : List α), List.ibelow t → motive t) → motive t :=
fun {α} {motive} t F_1 => (
  @List.rec α (fun t => And (motive t) (@List.ibelow α motive t))
    ⟨F_1 [] True.intro, True.intro⟩
    (fun head tail tail_ih => ⟨F_1 (head :: tail) ⟨tail_ih, True.intro⟩, ⟨tail_ih, True.intro⟩⟩)
    t
  ).1
```
-/
def mkBRecOnOrBInductionOn (indName : Name) (ind : Bool) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo indName | return
  unless indVal.isRec do return
  if ← isPropFormerType indVal.type then return
  let recName := mkRecName indName
  let .recInfo recVal ← getConstInfo recName | return
  unless recVal.numMotives = indVal.all.length do
    /-
    The mutual declaration containing `declName` contains nested inductive datatypes.
    We don't support this kind of declaration here yet. We probably never will :)
    To support it, we will need to generate an auxiliary `below` for each nested inductive
    type since their default `below` is not good here. For example, at
    ```
    inductive Term
    | var : String -> Term
    | app : String -> List Term -> Term
    ```
    The `List.below` is not useful since it will not allow us to recurse over the nested terms.
    We need to generate another one using the auxiliary recursor `Term.rec_1` for `List Term`.
    -/
    return

  let lvl::lvls := recVal.levelParams.map (Level.param ·)
    | throwError "recursor {recName} has no levelParams"
  let lvlParam := recVal.levelParams.head!
  -- universe parameter names of brecOn/binductionOn
  let blps := if ind then recVal.levelParams.tail!  else recVal.levelParams
  -- universe arguments of below/ibelow
  let blvls := if ind then lvls else lvl::lvls

  let .some ⟨idx, _⟩ := indVal.all.toArray.indexOf? indName
    | throwError m!"Did not find {indName} in {indVal.all}"

  let .some ilvl ← typeFormerTypeLevel indVal.type
    | throwError "type {indVal.type} of inductive {indVal.name} not a type former?"
  -- universe level of the resultant type
  let rlvl : Level :=
    if ind then
      0
    else if indVal.isReflexive then
      if let .max 1 lvl := ilvl then
        mkLevelMax' (.succ lvl) lvl
      else
        mkLevelMax' (.succ lvl) ilvl
    else
      mkLevelMax' 1 lvl

  let refType :=
    if ind then
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

    -- One `below` for each type former (same parameters)
    let belows := indVal.all.toArray.map fun n =>
      let belowName := if ind then mkIBelowName n else mkBelowName n
      mkAppN (.const belowName blvls) (params ++ typeFormers)

    -- create types of functionals (one for each type former)
    --   (F_1 : (t : List α) → (f : List.below t) → motive t)
    -- and bring parameters of that type into scope
    let mut fDecls : Array (Name × (Array Expr -> MetaM Expr)) := #[]
    for typeFormer in typeFormers, below in belows, i in [:typeFormers.size] do
      let fType ← forallTelescope (← inferType typeFormer) fun targs _ => do
        withLocalDeclD `f (mkAppN below targs) fun f =>
          mkForallFVars (targs.push f) (mkAppN typeFormer targs)
      let fName := .mkSimple s!"F_{i + 1}"
      fDecls := fDecls.push (fName, fun _ => pure fType)
    withLocalDeclsD fDecls fun fs => do
      let mut val := .const recName (rlvl :: lvls)
      -- add parameters
      val := mkAppN val params
      -- add type formers
      for typeFormer in typeFormers, below in belows do
        -- example: (motive := fun t => PProd (motive t) (@List.below α motive t))
        let arg ← forallTelescope (← inferType typeFormer) fun targs _ => do
          let cType := mkAppN typeFormer targs
          let belowType := mkAppN below targs
          let arg ← mkPProd cType belowType
          mkLambdaFVars targs arg
        val := .app val arg
      -- add minor premises
      for minor in minors do
        let arg ← buildBRecOnMinorPremise rlvl typeFormers belows fs (← inferType minor)
        val := .app val arg
      -- add indices and major premise
      val := mkAppN val remaining
      -- project out first component
      val ← mkPProdFst val

      -- All paramaters of `.rec` besides the `minors` become parameters of `.bRecOn`, and the `fs`
      let below_params := params ++ typeFormers ++ remaining ++ fs
      let type ← mkForallFVars below_params (mkAppN typeFormers[idx]! remaining)
      val ← mkLambdaFVars below_params val

      let name := if ind then mkBInductionOnName indName else mkBRecOnName indName
      mkDefinitionValInferrringUnsafe name blps type val .abbrev

  addDecl (.defnDecl decl)
  setReducibleAttribute decl.name
  modifyEnv fun env => markAuxRecursor env decl.name
  modifyEnv fun env => addProtected env decl.name

def mkBRecOn (declName : Name) : MetaM Unit := mkBRecOnOrBInductionOn declName false
def mkBInductionOn (declName : Name) : MetaM Unit := mkBRecOnOrBInductionOn declName true
