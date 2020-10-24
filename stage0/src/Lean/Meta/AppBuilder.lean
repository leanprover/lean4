#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Structure
import Lean.Util.Recognizers
import Lean.Meta.SynthInstance
import Lean.Meta.Check

namespace Lean.Meta

variables {m : Type → Type} [MonadLiftT MetaM m]

private def mkIdImp (e : Expr) : MetaM Expr := do
  let type ← inferType e
  let u    ← getLevel type
  pure $ mkApp2 (mkConst `id [u]) type e
/-- Return `id e` -/
def mkId (e : Expr) : m Expr :=
  liftMetaM $ mkIdImp e

private def mkExpectedTypeHintImp (e : Expr) (expectedType : Expr) : MetaM Expr := do
  let u ← getLevel expectedType
  pure $ mkApp2 (mkConst `id [u]) expectedType e
/-- Given `e` s.t. `inferType e` is definitionally equal to `expectedType`, return
    term `@id expectedType e`. -/
def mkExpectedTypeHint (e : Expr) (expectedType : Expr) : m Expr :=
  liftMetaM $ mkExpectedTypeHintImp e expectedType

private def mkEqImp (a b : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getLevel aType
  pure $ mkApp3 (mkConst `Eq [u]) aType a b
def mkEq (a b : Expr) : m Expr :=
  liftMetaM $ mkEqImp a b

private def mkHEqImp (a b : Expr) : MetaM Expr := do
  let aType ← inferType a
  let bType ← inferType b
  let u ← getLevel aType
  pure $ mkApp4 (mkConst `HEq [u]) aType a bType b
def mkHEq (a b : Expr) : m Expr :=
  liftMetaM $ mkHEqImp a b

private def mkEqReflImp (a : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getLevel aType
  pure $ mkApp2 (mkConst `Eq.refl [u]) aType a
def mkEqRefl (a : Expr) : m Expr :=
  liftMetaM $ mkEqReflImp a

private def mkHEqReflImp (a : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getLevel aType
  pure $ mkApp2 (mkConst `HEq.refl [u]) aType a
def mkHEqRefl (a : Expr) : m Expr :=
  liftMetaM $ mkHEqReflImp a

private def infer (h : Expr) : MetaM Expr := do
  let hType ← inferType h
  whnfD hType

private def hasTypeMsg (e type : Expr) : MessageData :=
  msg!"{indentExpr e}\nhas type{indentExpr type}"

private def throwAppBuilderException {α} (op : Name) (msg : MessageData) : MetaM α :=
  throwError! "AppBuilder for '{op}', {msg}"

private def mkEqSymmImp (h : Expr) : MetaM Expr :=
  if h.isAppOf `Eq.refl then
    pure h
  else do
    let hType ← infer h
    match hType.eq? with
    | some (α, a, b) => do let u ← getLevel α; pure $ mkApp4 (mkConst `Eq.symm [u]) α a b h
    | none => throwAppBuilderException `Eq.symm ("equality proof expected" ++ hasTypeMsg h hType)
def mkEqSymm (h : Expr) : m Expr :=
  liftMetaM $ mkEqSymmImp h

private def mkEqTransImp (h₁ h₂ : Expr) : MetaM Expr :=
  if h₁.isAppOf `Eq.refl then pure h₂
  else if h₂.isAppOf `Eq.refl then pure h₁
  else do
    let hType₁ ← infer h₁
    let hType₂ ← infer h₂
    match hType₁.eq?, hType₂.eq? with
    | some (α, a, b), some (_, _, c) =>
      do let u ← getLevel α; pure $ mkApp6 (mkConst `Eq.trans [u]) α a b c h₁ h₂
    | none, _ => throwAppBuilderException `Eq.trans ("equality proof expected" ++ hasTypeMsg h₁ hType₁)
    | _, none => throwAppBuilderException `Eq.trans ("equality proof expected" ++ hasTypeMsg h₂ hType₂)
def mkEqTrans (h₁ h₂ : Expr) : m Expr :=
  liftMetaM $ mkEqTransImp h₁ h₂

private def mkHEqSymmImp (h : Expr) : MetaM Expr :=
  if h.isAppOf `HEq.refl then pure h
  else do
    let hType ← infer h
    match hType.heq? with
    | some (α, a, β, b) => do let u ← getLevel α; pure $ mkApp5 (mkConst `HEq.symm [u]) α β a b h
    | none => throwAppBuilderException `HEq.symm ("heterogeneous equality proof expected" ++ hasTypeMsg h hType)
def mkHEqSymm (h : Expr) : m Expr :=
  liftMetaM $ mkHEqSymmImp h

private def mkHEqTransImp (h₁ h₂ : Expr) : MetaM Expr := do
  if h₁.isAppOf `HEq.refl then pure h₂
  else if h₂.isAppOf `HEq.refl then pure h₁
  else do
    let hType₁ ← infer h₁
    let hType₂ ← infer h₂
    match hType₁.heq?, hType₂.heq? with
    | some (α, a, β, b), some (_, _, γ, c) =>
      let u ← getLevel α; pure $ mkApp8 (mkConst `HEq.trans [u]) α β γ a b c h₁ h₂
    | none, _ => throwAppBuilderException `HEq.trans ("heterogeneous equality proof expected" ++ hasTypeMsg h₁ hType₁)
    | _, none => throwAppBuilderException `HEq.trans ("heterogeneous equality proof expected" ++ hasTypeMsg h₂ hType₂)
def mkHEqTrans (h₁ h₂ : Expr) : m Expr :=
  liftMetaM $ mkHEqTransImp h₁ h₂

private def mkEqOfHEqImp (h : Expr) : MetaM Expr := do
  let hType ← infer h
  match hType.heq? with
  | some (α, a, β, b) =>
    unless (← isDefEq α β) do
      throwAppBuilderException `eqOfHEq msg!"heterogeneous equality types are not definitionally equal{indentExpr α}\nis not definitionally equal to{indentExpr β}"
    let u ← getLevel α
    pure $ mkApp4 (mkConst `eqOfHEq [u]) α a b h
  | _ =>
    throwAppBuilderException `HEq.trans msg!"heterogeneous equality proof expected{indentExpr h}"
def mkEqOfHEq (h : Expr) : m Expr :=
  liftMetaM $ mkEqOfHEqImp h

private def mkCongrArgImp (f h : Expr) : MetaM Expr := do
  let hType ← infer h
  let fType ← infer f
  match fType.arrow?, hType.eq? with
  | some (α, β), some (_, a, b) =>
    let u ← getLevel α; let v ← getLevel β; pure $ mkApp6 (mkConst `congrArg [u, v]) α β a b f h
  | none, _ => throwAppBuilderException `congrArg ("non-dependent function expected" ++ hasTypeMsg f fType)
  | _, none => throwAppBuilderException `congrArg ("equality proof expected" ++ hasTypeMsg h hType)
def mkCongrArg (f h : Expr) : m Expr :=
  liftMetaM $ mkCongrArgImp f h

private def mkCongrFunImp (h a : Expr) : MetaM Expr := do
  let hType ← infer h
  match hType.eq? with
  | some (ρ, f, g) => do
    let ρ ← whnfD ρ
    match ρ with
    | Expr.forallE n α β _ => do
      let β' := Lean.mkLambda n BinderInfo.default α β
      let u ← getLevel α
      let v ← getLevel (mkApp β' a)
      pure $ mkApp6 (mkConst `congrFun [u, v]) α β' f g h a
    | _ => throwAppBuilderException `congrFun ("equality proof between functions expected" ++ hasTypeMsg h hType)
  | _ => throwAppBuilderException `congrFun ("equality proof expected" ++ hasTypeMsg h hType)
def mkCongrFun (h a : Expr) : m Expr :=
  liftMetaM $ mkCongrFunImp h a

private def mkCongrImp (h₁ h₂ : Expr) : MetaM Expr := do
  let hType₁ ← infer h₁
  let hType₂ ← infer h₂
  match hType₁.eq?, hType₂.eq? with
  | some (ρ, f, g), some (α, a, b) => do
    let ρ ← whnfD ρ
    match ρ.arrow? with
    | some (_, β) => do
      let u ← getLevel α
      let v ← getLevel β
      pure $ mkApp8 (mkConst `congr [u, v]) α β f g a b h₁ h₂
    | _ => throwAppBuilderException `congr ("non-dependent function expected" ++ hasTypeMsg h₁ hType₁)
  | none, _ => throwAppBuilderException `congr ("equality proof expected" ++ hasTypeMsg h₁ hType₁)
  | _, none => throwAppBuilderException `congr ("equality proof expected" ++ hasTypeMsg h₂ hType₂)
def mkCongr (h₁ h₂ : Expr) : m Expr :=
  liftMetaM $ mkCongrImp h₁ h₂

private def mkAppMFinal (methodName : Name) (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← getMVarDecl mvarId
    let mvarVal  ← synthInstance mvarDecl.type
    assignExprMVar mvarId mvarVal
  let result ← instantiateMVars (mkAppN f args)
  if (← hasAssignableMVar result) then throwAppBuilderException methodName ("result contains metavariables" ++ indentExpr result)
  pure result

private partial def mkAppMArgs (f : Expr) (fType : Expr) (xs : Array Expr) : MetaM Expr :=
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
    if i >= xs.size then
      mkAppMFinal `mkAppM f args instMVars
    else match type with
      | Expr.forallE n d b c =>
        let d  := d.instantiateRevRange j args.size args
        match c.binderInfo with
        | BinderInfo.implicit     =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) instMVars
        | BinderInfo.instImplicit =>
          let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
          loop b i j (args.push mvar) (instMVars.push mvar.mvarId!)
        | _ =>
          let x := xs[i]
          let xType ← inferType x
          if (← isDefEq d xType) then
            loop b (i+1) j (args.push x) instMVars
          else
            throwAppTypeMismatch (mkAppN f args) x
      | type =>
        let type := type.instantiateRevRange j args.size args
        let type ← whnfD type
        if type.isForall then
          loop type i args.size args instMVars
        else
          throwAppBuilderException `mkAppM msg!"too many explicit arguments provided to{indentExpr f}\narguments{indentD xs}"
  loop fType 0 0 #[] #[]

private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.lparams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType := cinfo.instantiateTypeLevelParams us
  pure (f, fType)

/--
  Return the application `constName xs`.
  It tries to fill the implicit arguments before the last element in `xs`.

  Remark:
  ``mkAppM `arbitrary #[α]`` returns `@arbitrary.{u} α` without synthesizing
  the implicit argument occurring after `α`.
  Given a `x : (([Decidable p] → Bool) × Nat`, ``mkAppM `Prod.fst #[x]`` returns `@Prod.fst ([Decidable p] → Bool) Nat x`
-/
def mkAppM (constName : Name) (xs : Array Expr) : m Expr := liftMetaM do
  traceCtx `Meta.appBuilder $ withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    let r ← mkAppMArgs f fType xs
    trace[Meta.appBuilder]! "constName: {constName}, xs: {xs}, result: {r}"
    pure r

private partial def mkAppOptMAux (f : Expr) (xs : Array (Option Expr)) : Nat → Array Expr → Nat → Array MVarId → Expr → MetaM Expr
  | i, args, j, instMVars, Expr.forallE n d b c => do
    let d  := d.instantiateRevRange j args.size args
    if h : i < xs.size then
      match xs.get ⟨i, h⟩ with
      | none =>
        match c.binderInfo with
        | BinderInfo.instImplicit => do
          let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
          mkAppOptMAux f xs (i+1) (args.push mvar) j (instMVars.push mvar.mvarId!) b
        | _                       => do
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          mkAppOptMAux f xs (i+1) (args.push mvar) j instMVars b
      | some x =>
        let xType ← inferType x
        if (← isDefEq d xType) then
          mkAppOptMAux f xs (i+1) (args.push x) j instMVars b
        else
          throwAppTypeMismatch (mkAppN f args) x
    else
      mkAppMFinal `mkAppOptM f args instMVars
  | i, args, j, instMVars, type => do
    let type := type.instantiateRevRange j args.size args
    let type ← whnfD type
    if type.isForall then
      mkAppOptMAux f xs i args args.size instMVars type
    else if i == xs.size then
      mkAppMFinal `mkAppOptM f args instMVars
    else do
      let xs : Array Expr := xs.foldl (fun r x? => match x? with | none => r | some x => r.push x) #[]
      throwAppBuilderException `mkAppOptM ("too many arguments provided to" ++ indentExpr f ++ Format.line ++ "arguments" ++ xs)

/--
  Similar to `mkAppM`, but it allows us to specify which arguments are provided explicitly using `Option` type.
  Example:
  Given `HasPure.pure {m : Type u → Type v} [HasPure m] {α : Type u} (a : α) : m α`,
  ```
  mkAppOptM `HasPure.pure #[m, none, none, a]
  ```
  returns a `HasPure.pure` application if the instance `HasPure m` can be synthesized, and the universes match.
  Note that,
  ```
  mkAppM `HasPure.pure #[a]
  ```
  fails because the only explicit argument `(a : α)` is not sufficient for inferring the remaining arguments,
  we would need the expected type. -/
def mkAppOptM (constName : Name) (xs : Array (Option Expr)) : m Expr := liftMetaM do
  traceCtx `Meta.appBuilder $ withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    mkAppOptMAux f xs 0 #[] 0 #[] fType

private def mkEqNDRecImp (motive h1 h2 : Expr) : MetaM Expr := do
  if h2.isAppOf `Eq.refl then pure h1
  else
    let h2Type ← infer h2
    match h2Type.eq? with
    | none => throwAppBuilderException `Eq.ndrec ("equality proof expected" ++ hasTypeMsg h2 h2Type)
    | some (α, a, b) =>
      let u2 ← getLevel α
      let motiveType ← infer motive
      match motiveType with
      | Expr.forallE _ _ (Expr.sort u1 _) _ =>
        pure $ mkAppN (mkConst `Eq.ndrec [u1, u2]) #[α, a, motive, h1, b, h2]
      | _ => throwAppBuilderException `Eq.ndrec ("invalid motive" ++ indentExpr motive)
def mkEqNDRec (motive h1 h2 : Expr) : m Expr :=
  liftMetaM $ mkEqNDRecImp motive h1 h2

private def mkEqRecImp (motive h1 h2 : Expr) : MetaM Expr := do
  if h2.isAppOf `Eq.refl then pure h1
  else
    let h2Type ← infer h2
    match h2Type.eq? with
    | none => throwAppBuilderException `Eq.rec ("equality proof expected" ++ indentExpr h2)
    | some (α, a, b) =>
      let u2 ← getLevel α
      let motiveType ← infer motive
      match motiveType with
      | Expr.forallE _ _ (Expr.forallE _ _ (Expr.sort u1 _) _) _ =>
        pure $ mkAppN (mkConst `Eq.rec [u1, u2]) #[α, a, motive, h1, b, h2]
      | _ => throwAppBuilderException `Eq.rec ("invalid motive" ++ indentExpr motive)
def mkEqRec (motive h1 h2 : Expr) : m Expr :=
  liftMetaM $ mkEqRecImp motive h1 h2

def mkEqMP (eqProof pr : Expr) : m Expr :=
  mkAppM `Eq.mp #[eqProof, pr]

def mkEqMPR (eqProof pr : Expr) : m Expr :=
  mkAppM `Eq.mpr #[eqProof, pr]

private def mkNoConfusionImp (target : Expr) (h : Expr) : MetaM Expr := do
  let type ← inferType h
  let type ← whnf type
  match type.eq? with
  | none           => throwAppBuilderException `noConfusion ("equality expected" ++ hasTypeMsg h type)
  | some (α, a, b) =>
    let α ← whnf α
    matchConstInduct α.getAppFn (fun _ => throwAppBuilderException `noConfusion ("inductive type expected" ++ indentExpr α)) fun v us => do
      let u ← getLevel target
      pure $ mkAppN (mkConst (mkNameStr v.name "noConfusion") (u :: us)) (α.getAppArgs ++ #[target, a, b, h])
def mkNoConfusion (target : Expr) (h : Expr) : m Expr :=
  liftMetaM $ mkNoConfusionImp target h

def mkPure (monad : Expr) (e : Expr) : m Expr :=
  mkAppOptM `HasPure.pure #[monad, none, none, e]

/--
  `mkProjection s fieldName` return an expression for accessing field `fieldName` of the structure `s`.
  Remark: `fieldName` may be a subfield of `s`. -/
private partial def mkProjectionImp : Expr → Name → MetaM Expr
  | s, fieldName => do
    let type ← inferType s
    let type ← whnf type
    match type.getAppFn with
    | Expr.const structName us _ =>
      let env ← getEnv
      unless isStructureLike env structName do throwAppBuilderException `mkProjection ("structure expected" ++ hasTypeMsg s type)
      match getProjFnForField? env structName fieldName with
      | some projFn =>
        let params := type.getAppArgs
        pure $ mkApp (mkAppN (mkConst projFn us) params) s
      | none => do
        let fields := getStructureFields env structName
        let r? ← fields.findSomeM? fun fieldName' => do
          match isSubobjectField? env structName fieldName' with
          | none   => pure none
          | some _ =>
            let parent ← mkProjectionImp s fieldName'
            (do let r ← mkProjectionImp parent fieldName; pure $ some r)
            <|>
            pure none
        match r? with
        | some r => pure r
        | none   => throwAppBuilderException `mkProjectionn ("invalid field name '" ++ toString fieldName ++ "' for" ++ hasTypeMsg s type)
    | _ => throwAppBuilderException `mkProjectionn ("structure expected" ++ hasTypeMsg s type)
def mkProjection (s : Expr) (fieldName : Name) : m Expr :=
  liftMetaM $ mkProjectionImp s fieldName

private def mkListLitAux (nil : Expr) (cons : Expr) : List Expr → Expr
  | []    => nil
  | x::xs => mkApp (mkApp cons x) (mkListLitAux nil cons xs)

private def mkListLitImp (type : Expr) (xs : List Expr) : MetaM Expr := do
  let u   ← getDecLevel type
  let nil := mkApp (mkConst `List.nil [u]) type
  match xs with
  | [] => pure nil
  | _  =>
    let cons := mkApp (mkConst `List.cons [u]) type
    pure $ mkListLitAux nil cons xs
def mkListLit (type : Expr) (xs : List Expr) : m Expr :=
  liftMetaM $ mkListLitImp type xs

def mkArrayLit (type : Expr) (xs : List Expr) : m Expr := liftMetaM do
  let u ← getDecLevel type
  let listLit ← mkListLit type xs
  pure (mkApp (mkApp (mkConst `List.toArray [u]) type) listLit)

def mkSorry (type : Expr) (synthetic : Bool) : m Expr := liftMetaM do
  let u ← getLevel type
  pure $ mkApp2 (mkConst `sorryAx [u]) type (toExpr synthetic)

/-- Return `Decidable.decide p` -/
def mkDecide (p : Expr) : m Expr :=
  mkAppOptM `Decidable.decide #[p, none]

/-- Return a proof for `p : Prop` using `decide p` -/
def mkDecideProof (p : Expr) : m Expr := liftMetaM do
  let decP      ← mkDecide p
  let decEqTrue ← mkEq decP (mkConst `Bool.true)
  let h         ← mkEqRefl (mkConst `Bool.true)
  let h         ← mkExpectedTypeHint h decEqTrue
  mkAppM `ofDecideEqTrue #[h]

/-- Return `a < b` -/
def mkLt (a b : Expr) : m Expr :=
  mkAppM `HasLess.Less #[a, b]

/-- Return `a <= b` -/
def mkLe (a b : Expr) : m Expr :=
  mkAppM `HasLessEq.LessEq #[a, b]

/-- Return `arbitrary α` -/
def mkArbitrary (α : Expr) : m Expr :=
  mkAppOptM `arbitrary #[α, none]

builtin_initialize registerTraceClass `Meta.appBuilder

end Lean.Meta
