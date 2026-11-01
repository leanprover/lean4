/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Meta.Basic
public import Lean.Meta.InferType
public import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.CompletionName
import Lean.Meta.NatTable
import Lean.Elab.App

namespace Lean

open Meta

-- Right-associates the top-most `max`s to work around #5695 for prettier code
def reassocMax (l : Level) : Level :=
  let lvls := maxArgs l #[]
  let last := lvls.back!
  lvls.pop.foldr mkLevelMax last
where
  maxArgs (l : Level) (lvls : Array Level) : Array Level :=
  match l with
  | .max l1 l2 => maxArgs l2 (maxArgs l1 lvls)
  | _ => lvls.push l

def maxLevels (es : Array Expr) : MetaM Level := do
  assert! es.size > 0
  let mut maxLevel ← getLevel es[0]!
  for e in es[1...*] do
    let l ← getLevel e
    maxLevel := mkLevelMax' maxLevel l
  return reassocMax maxLevel.normalize

def mkPULift (r : Level) (t : Expr) : MetaM Expr := do
  let s ← getLevel t
  return mkApp (mkConst `PULift [r,s]) t

def withMkPULiftUp (t : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let t ← whnf t
  if t.isAppOfArity `PULift 1 then
    let t' := t.appArg!
    let e ← k t'
    return mkApp2 (mkConst `PULift.up (t.appFn!.constLevels!)) t' e
  else
    throwError "withMkPULiftUp: expected PULift type, got {t}"

def mkPULiftDown (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  if t.isAppOfArity `PULift 1 then
    let t' := t.appArg!
    return mkApp2 (mkConst `PULift.down t.appFn!.constLevels!) t' e
  else
    throwError "mkULiftDown: expected ULift type, got {t}"

def mkNatLookupTableLifting (n : Expr) (es : Array Expr) : MetaM Expr := do
  let u ← maxLevels es
  let u' := reassocMax (mkLevelMax' u 1).normalize
  let es ← es.mapM (mkPULift u)
  mkNatLookupTable n (.sort u') es

def mkCtorElimTypeName (indName : Name) : Name :=
  Name.str indName "ctorElimType"

public def mkCtorElimName (indName : Name) : Name :=
  Name.str indName "ctorElim"

def asPrivateAs (n1 n2 : Name) : Name :=
  match privatePrefix? n2 with
  | some p => Name.appendCore p (privateToUserName n1)
  | none => (privateToUserName n1)

public def mkConstructorElimName (indName : Name) (conName : Name) : Name :=
  asPrivateAs (Name.str conName "elim") indName

def mkCtorElimType (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  if info.numCtors = 0 then return
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let e ← forallTelescope casesOnInfo.type fun xs _ =>
    let params : Array Expr := xs[:info.numParams]
    let motive := xs[info.numParams]!
    -- let indices : Array Expr := xs[info.numParams + 1:info.numParams + 1 + info.numIndices]
    -- let majorArg := xs[info.numParams + 1 + info.numIndices]!
    let alts : Array Expr := xs[info.numParams + 1 + info.numIndices + 1:]
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
      let es ← alts.mapM inferType
      let e ← mkNatLookupTableLifting ctorIdx es
      mkLambdaFVars (params ++ #[motive, ctorIdx]) e

  let declName := mkCtorElimTypeName indName
  addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)
  ))
  modifyEnv fun env => addToCompletionBlackList env declName
  modifyEnv fun env => addProtected env declName
  setReducibleAttribute declName

def mkIndCtorElim (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let CtorElimTypeName := mkCtorElimTypeName indName
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let e ← forallTelescope casesOnInfo.type fun xs _ =>
    let params : Array Expr := xs[:info.numParams]
    let motive := xs[info.numParams]!
    let indices : Array Expr := xs[info.numParams + 1:info.numParams + 1 + info.numIndices]
    let majorArg := xs[info.numParams + 1 + info.numIndices]!
    let ism := indices.push majorArg
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
    let kTypeF := mkAppN (mkConst CtorElimTypeName (v :: us)) (params.push motive)
    let kType := mkApp kTypeF ctorIdx
    let ctorApp := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ ism)
    let hType ← mkEq ctorIdx ctorApp
    withLocalDeclD `h hType fun h => do
    withLocalDeclD `k kType fun k => do
    let motive' ← mkLambdaFVars ism <|
      (← mkArrow hType (mkAppN motive ism))
    let e := mkConst casesOnInfo.name (v :: us)
    let e := mkAppN e params
    let e := mkApp e motive'
    let e := mkAppN e ism
    let alts ← info.ctors.toArray.mapIdxM fun i ctorName => do
      let ctor := mkAppN (mkConst ctorName us) params
      let ctorType ← inferType ctor
      forallTelescope ctorType fun zs _ctorRet => do
        -- Here we let the typecheker reduce the `ctorIdx` application
          let heq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) ctorIdx (mkRawNatLit i)
          withLocalDeclD `h heq fun h => do
            let e ← mkEqNDRec (motive := kTypeF) k h
            let e ← mkPULiftDown e
            let e := mkAppN e zs
            -- ``Eq.ndrec
            mkLambdaFVars (zs.push h) e
    let e := mkAppN e alts
    let e := mkApp e h
    mkLambdaFVars (params ++ #[motive, ctorIdx] ++ ism ++ #[h, k]) e

  let declName := mkCtorElimName indName
  addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)
  ))
  modifyEnv fun env => markAuxRecursor env declName
  modifyEnv fun env => addToCompletionBlackList env declName
  modifyEnv fun env => addProtected env declName
  setReducibleAttribute declName

/--
Specialies `T.CtorElim` for each constructor as `T.ctor.elim`.
-/
def mkConstructorElim (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let CtorElimName := mkCtorElimName indName
  let CtorElimTypeName := mkCtorElimTypeName indName
  let casesOnInfo ← getConstVal casesOnName
  -- Now specialize for each constructor
  for i in [:info.numCtors] do
    let declName := mkConstructorElimName indName info.ctors[i]!
    let e ← forallTelescope casesOnInfo.type fun xs _ => do
      let params : Array Expr := xs[:info.numParams]
      let motive := xs[info.numParams]!
      let indices : Array Expr := xs[info.numParams + 1:info.numParams + 1 + info.numIndices]
      let majorArg := xs[info.numParams + 1 + info.numIndices]!
      let ism := indices.push majorArg
      let alts := xs[info.numParams + 1 + info.numIndices + 1:]
      let alt := alts[i]!
      let ctorApp := mkAppN (mkConst (mkCtorIdxName indName) us) (params ++ ism)
      let hType ← mkEq ctorApp (mkRawNatLit i)
      withLocalDeclD `h hType fun h => do
        let e := mkConst CtorElimName (v :: us)
        let e := mkAppN e params
        let e := mkApp e motive
        let e := mkApp e (mkRawNatLit i)
        let e := mkAppN e ism
        let e := mkApp e (← mkEqSymm h)
        let CtorElimTypeApp := mkAppN (mkConst CtorElimTypeName (v :: us)) ((params.push motive).push (mkRawNatLit i))
        let e := mkApp e (← withMkPULiftUp CtorElimTypeApp fun _ => pure alt)
        mkLambdaFVars (params ++ #[motive] ++ ism ++ #[h, alt]) e
    let declType ← inferType e

    addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
      (name        := declName)
      (levelParams := casesOnInfo.levelParams)
      (type        := declType)
      (value       := e)
      (hints       := ReducibilityHints.abbrev)
    ))
    modifyEnv fun env => markAuxRecursor env declName
    modifyEnv fun env => markSparseCasesOn env declName
    modifyEnv fun env => addToCompletionBlackList env declName
    modifyEnv fun env => addProtected env declName
    Elab.Term.elabAsElim.setTag declName
    setReducibleAttribute declName

public def mkCtorElim (indName : Name) : MetaM Unit := do
  -- We need the `.ctorIdx` function to exist
  unless (← getEnv).contains (mkCtorIdxName indName) do return
  let .inductInfo indVal ← getConstInfo indName | return
  -- Do not do anything if there are not multiple constructors
  unless indVal.numCtors > 1 do return
  -- Do not do anything unless its a type and can elim to type
  if (← isPropFormerType indVal.type) then return
  unless (← isLargeEliminating indName) do return

  -- Expose if indName is not private
  withExporting (isExporting := ! isPrivateName indName) do
    mkCtorElimType indName
    mkIndCtorElim indName
    mkConstructorElim indName


/--
Generate the `.toCtorIdx` and `.ctor.elim` definitions for the given inductive.

This attribute is only meant to be used in `Init.Prelude` to build these constructions for
types where we did not generate them immediately (due to `set_option genCtorIdx false`).
-/
@[builtin_doc]
builtin_initialize registerBuiltinAttribute {
  name := `gen_constructor_elims
  descr := "generate the `.toCtorIdx` and `.ctor.elim` definitions for the given inductive"
  add := fun decl _stx kind => MetaM.run' do
    unless kind == .global do throwAttrMustBeGlobal `gen_constructor_elims kind
    mkCtorIdx decl
    mkCtorElim decl
}

/--
Given `discr` whose type is an inductive type, create a dependent if-then-else expression of type
`resultType` that checks for `discr.ctorIdx = rhs`, calling `ctorEqBranch` with a proof of
`discr.ctorIdx = rhs` and `fallbackBranch` with a proof of `¬ discr.ctorIdx = rhs`.

If the inductive only has one constructor, this function assumes that the `rhs` is definitionally
equal to zero (e.g. a `mkCtorIdxApp` for the same inductive or just the constant `0`) and
only calls `ctorEqBranch` with a proof that `0 = 0`.
-/
public def Meta.matchCtorIdxEq [Monad m] [MonadEnv m] [MonadError m]
    [MonadControlT MetaM m] [MonadLiftT MetaM m] (discr : Expr) (rhs : Expr) (resultType : Expr)
    (ctorEqBranch : Expr → m Expr) (fallbackBranch : Expr → m Expr) :
    m Expr := do
  let cidx ← mkCtorIdxApp discr
  if cidx == mkRawNatLit 0 then
    return ← ctorEqBranch (mkApp2 (.const ``rfl [1]) Nat.mkType (mkRawNatLit 0))
  let natEq := mkApp3 (.const ``Eq [1]) Nat.mkType cidx rhs
  let natDecEq := mkApp2 (.const ``Nat.decEq []) cidx rhs
  let trueBranch ← withLocalDeclD `ctorIdx_eq natEq fun hcidx => do
    mkLambdaFVars #[hcidx] <| ← ctorEqBranch hcidx
  let falseBranch ← withLocalDeclD `ctorIdx_ne (mkNot natEq) fun hcidx => do
    mkLambdaFVars #[hcidx] <| ← fallbackBranch hcidx
  return mkApp5 (.const ``dite [← getLevel resultType])
    resultType natEq natDecEq trueBranch falseBranch

/--
Given `discr` whose type is an inductive type and
`ctorIdxEq : discr.ctorIdx = <constructor index of targetCtor>`, constructs a constructor
eliminator application of type `resultType`, computing the motive using `computeMotive` applied to
the expected type of the motive and the indices of `discr` and computing the alternative by calling
`alt` with the inductive info, constructor info, the fields, the constructor application, and the
new type.

`computeMotive _ indices` is expected to return `motive` such that `motive` applied to `indices`
and `discr` is definitionally equal to `resultType`.
-/
public def Meta.mkCtorElimAppAux [Monad m] [MonadEnv m] [MonadError m]
    [MonadControlT MetaM m] [MonadLiftT MetaM m]
    (discr : Expr) (resultType : Expr) (targetCtor : Name) (ctorIdxEq : Expr)
    (alt : InductiveVal → ConstructorVal → (fields : Array Expr) → (ctorApp : Expr) →
      (newType : Expr) → m Expr)
    (computeMotive : (motiveType : Expr) → (indices : Array Expr) → m Expr) : m Expr := do
  let ctorInfo ← getConstInfoCtor targetCtor
  let indInfo ← getConstInfoInduct ctorInfo.induct
  let type ← whnfD (← inferType discr)
  type.withApp fun fn args => do
    let .const nm us := fn |
      throwError "Invalid input to `{.ofConstName decl_name%}`; \
        expected inductive type at{indentExpr type}"
    unless nm = indInfo.name do
      throwError "Invalid input to `{.ofConstName decl_name%}`; \
        expected `{.ofConstName targetCtor}` to be a constructor of `{.ofConstName nm}`"
    assert! args.size = indInfo.numParams + indInfo.numIndices
    let resultSort ← getLevel resultType
    let induct := indInfo.name
    let params := args.take indInfo.numParams
    let indices := args.drop indInfo.numParams
    let useCasesOn := indInfo.ctors matches [_]
    let elimName :=
      if useCasesOn then
        mkCasesOnName induct
      else
        mkConstructorElimName induct targetCtor
    let elimVal ← getConstVal elimName
    unless elimVal.levelParams.length = indInfo.levelParams.length + 1 do
      throwError "Error in `{.ofConstName decl_name%}`: \
        The inductive `{.ofConstName induct}` does not have large elimination"
    let mut elimApp := mkAppN (.const elimName (resultSort :: us)) params
    let elimType ← inferType elimApp
    let .forallE _ motiveType body _ := elimType | unreachable!
    let motive ← computeMotive motiveType indices
    let body := body.instantiate1 motive
    let vars := indices.push discr
    let mut body ← instantiateForall body vars
    elimApp := mkAppN (elimApp.app motive) vars
    unless useCasesOn do
      -- equality argument
      let .forallE _ _eqType body' _ := body | unreachable!
      body := body'
      elimApp := elimApp.app ctorIdxEq
    let .forallE _ altType _ _ := body | unreachable!
    let minor ← forallBoundedTelescope altType ctorInfo.numFields fun fields tgt => do
      let ctorApp := mkAppN (mkAppN (.const targetCtor us) params) fields
      mkLambdaFVars fields <| ← alt indInfo ctorInfo fields ctorApp tgt.headBeta
    elimApp := elimApp.app minor
    return elimApp

/--
Constructs a non-dependent constructor eliminator application of type `resultType` that matches on
`discr` with a proof `ctorIdxEq : discr.ctorIdx = <constructor index of targetCtor>`.

The alternative is computed by calling `alt` with the inductive info, constructor info, the fields,
and the constructor application.
-/
public def Meta.mkNondepCtorElim [Monad m] [MonadEnv m] [MonadError m]
    [MonadControlT MetaM m] [MonadLiftT MetaM m]
    (discr : Expr) (resultType : Expr) (targetCtor : Name) (ctorIdxEq : Expr)
    (alt : InductiveVal → ConstructorVal → Array Expr → Expr → m Expr) : m Expr := do
  mkCtorElimAppAux discr resultType targetCtor ctorIdxEq
    (fun ival cval fields ctorApp _ => alt ival cval fields ctorApp) -- ignore new result type
    (fun motiveType _ => forallTelescope motiveType (fun xs _ => mkLambdaFVars xs resultType))

/--
Given a free variable `discr` whose type is an inductive application with free variable indices
and a proof `ctorIdxEq : discr.ctorIdx = <constructor index of targetCtor>`, creates a dependent
constructor eliminator application of type `resultType`.

The alternatives are computed by calling `alt` with the inductive info, constructor info, the
fields, the constructor application and the new result type.
-/
public def Meta.mkDepCtorElim [Monad m] [MonadEnv m] [MonadError m]
    [MonadControlT MetaM m] [MonadLiftT MetaM m]
    (discr : Expr) (resultType : Expr) (targetCtor : Name) (ctorIdxEq : Expr)
    (alt : InductiveVal → ConstructorVal → Array Expr → Expr → Expr → m Expr) : m Expr := do
  mkCtorElimAppAux discr resultType targetCtor ctorIdxEq alt
    (fun _ indices => mkLambdaFVars (indices.push discr) resultType)
