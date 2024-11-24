/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Structure
import Lean.Util.Recognizers
import Lean.Meta.SynthInstance
import Lean.Meta.Check
import Lean.Meta.DecLevel

namespace Lean.Meta

/-- Return `id e` -/
def mkId (e : Expr) : MetaM Expr := do
  let type ← inferType e
  let u    ← getLevel type
  return mkApp2 (mkConst ``id [u]) type e

/--
  Given `e` s.t. `inferType e` is definitionally equal to `expectedType`, return
  term `@id expectedType e`. -/
def mkExpectedTypeHint (e : Expr) (expectedType : Expr) : MetaM Expr := do
  let u ← getLevel expectedType
  return mkApp2 (mkConst ``id [u]) expectedType e

/--
`mkLetFun x v e` creates the encoding for the `let_fun x := v; e` expression.
The expression `x` can either be a free variable or a metavariable, and the function suitably abstracts `x` in `e`.
NB: `x` must not be a let-bound free variable.
-/
def mkLetFun (x : Expr) (v : Expr) (e : Expr) : MetaM Expr := do
  let f ← mkLambdaFVars #[x] e
  let ety ← inferType e
  let α ← inferType x
  let β ← mkLambdaFVars #[x] ety
  let u1 ← getLevel α
  let u2 ← getLevel ety
  return mkAppN (.const ``letFun [u1, u2]) #[α, β, v, f]

/-- Return `a = b`. -/
def mkEq (a b : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getLevel aType
  return mkApp3 (mkConst ``Eq [u]) aType a b

/-- Return `HEq a b`. -/
def mkHEq (a b : Expr) : MetaM Expr := do
  let aType ← inferType a
  let bType ← inferType b
  let u ← getLevel aType
  return mkApp4 (mkConst ``HEq [u]) aType a bType b

/--
  If `a` and `b` have definitionally equal types, return `Eq a b`, otherwise return `HEq a b`.
-/
def mkEqHEq (a b : Expr) : MetaM Expr := do
  let aType ← inferType a
  let bType ← inferType b
  let u ← getLevel aType
  if (← isDefEq aType bType) then
    return mkApp3 (mkConst ``Eq [u]) aType a b
  else
    return mkApp4 (mkConst ``HEq [u]) aType a bType b

/-- Return a proof of `a = a`. -/
def mkEqRefl (a : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getLevel aType
  return mkApp2 (mkConst ``Eq.refl [u]) aType a

/-- Return a proof of `HEq a a`. -/
def mkHEqRefl (a : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getLevel aType
  return mkApp2 (mkConst ``HEq.refl [u]) aType a

/-- Given `hp : P` and `nhp : Not P` returns an instance of type `e`. -/
def mkAbsurd (e : Expr) (hp hnp : Expr) : MetaM Expr := do
  let p ← inferType hp
  let u ← getLevel e
  return mkApp4 (mkConst ``absurd [u]) p e hp hnp

/-- Given `h : False`, return an instance of type `e`. -/
def mkFalseElim (e : Expr) (h : Expr) : MetaM Expr := do
  let u ← getLevel e
  return mkApp2 (mkConst ``False.elim [u]) e h

private def infer (h : Expr) : MetaM Expr := do
  let hType ← inferType h
  whnfD hType

private def hasTypeMsg (e type : Expr) : MessageData :=
  m!"{indentExpr e}\nhas type{indentExpr type}"

private def throwAppBuilderException {α} (op : Name) (msg : MessageData) : MetaM α :=
  throwError "AppBuilder for '{op}', {msg}"

/-- Given `h : a = b`, returns a proof of `b = a`. -/
def mkEqSymm (h : Expr) : MetaM Expr := do
  if h.isAppOf ``Eq.refl then
    return h
  else
    let hType ← infer h
    match hType.eq? with
    | some (α, a, b) =>
      let u ← getLevel α
      return mkApp4 (mkConst ``Eq.symm [u]) α a b h
    | none => throwAppBuilderException ``Eq.symm ("equality proof expected" ++ hasTypeMsg h hType)

/-- Given `h₁ : a = b` and `h₂ : b = c` returns a proof of `a = c`. -/
def mkEqTrans (h₁ h₂ : Expr) : MetaM Expr := do
  if h₁.isAppOf ``Eq.refl then
    return h₂
  else if h₂.isAppOf ``Eq.refl then
    return h₁
  else
    let hType₁ ← infer h₁
    let hType₂ ← infer h₂
    match hType₁.eq?, hType₂.eq? with
    | some (α, a, b), some (_, _, c) =>
      let u ← getLevel α
      return mkApp6 (mkConst ``Eq.trans [u]) α a b c h₁ h₂
    | none, _ => throwAppBuilderException ``Eq.trans ("equality proof expected" ++ hasTypeMsg h₁ hType₁)
    | _, none => throwAppBuilderException ``Eq.trans ("equality proof expected" ++ hasTypeMsg h₂ hType₂)

/--
Similar to `mkEqTrans`, but arguments can be `none`.
`none` is treated as a reflexivity proof.
-/
def mkEqTrans? (h₁? h₂? : Option Expr) : MetaM (Option Expr) :=
  match h₁?, h₂? with
  | none, none       => return none
  | none, some h     => return h
  | some h, none     => return h
  | some h₁, some h₂ => mkEqTrans h₁ h₂

/-- Given `h : HEq a b`, returns a proof of `HEq b a`.  -/
def mkHEqSymm (h : Expr) : MetaM Expr := do
  if h.isAppOf ``HEq.refl then
    return h
  else
    let hType ← infer h
    match hType.heq? with
    | some (α, a, β, b) =>
      let u ← getLevel α
      return mkApp5 (mkConst ``HEq.symm [u]) α β a b h
    | none =>
      throwAppBuilderException ``HEq.symm ("heterogeneous equality proof expected" ++ hasTypeMsg h hType)

/-- Given `h₁ : HEq a b`, `h₂ : HEq b c`, returns a proof of `HEq a c`. -/
def mkHEqTrans (h₁ h₂ : Expr) : MetaM Expr := do
  if h₁.isAppOf ``HEq.refl then
    return h₂
  else if h₂.isAppOf ``HEq.refl then
    return h₁
  else
    let hType₁ ← infer h₁
    let hType₂ ← infer h₂
    match hType₁.heq?, hType₂.heq? with
    | some (α, a, β, b), some (_, _, γ, c) =>
      let u ← getLevel α
      return mkApp8 (mkConst ``HEq.trans [u]) α β γ a b c h₁ h₂
    | none, _ => throwAppBuilderException ``HEq.trans ("heterogeneous equality proof expected" ++ hasTypeMsg h₁ hType₁)
    | _, none => throwAppBuilderException ``HEq.trans ("heterogeneous equality proof expected" ++ hasTypeMsg h₂ hType₂)

/-- Given `h : HEq a b` where `a` and `b` have the same type, returns a proof of `Eq a b`. -/
def mkEqOfHEq (h : Expr) : MetaM Expr := do
  let hType ← infer h
  match hType.heq? with
  | some (α, a, β, b) =>
    unless (← isDefEq α β) do
      throwAppBuilderException ``eq_of_heq m!"heterogeneous equality types are not definitionally equal{indentExpr α}\nis not definitionally equal to{indentExpr β}"
    let u ← getLevel α
    return mkApp4 (mkConst ``eq_of_heq [u]) α a b h
  | _ =>
    throwAppBuilderException ``eq_of_heq m!"heterogeneous equality proof expected{indentExpr h}"

/--
If `e` is `@Eq.refl α a`, return `a`.
-/
def isRefl? (e : Expr) : Option Expr := do
  if e.isAppOfArity ``Eq.refl 2 then
    some e.appArg!
  else
    none

/--
If `e` is `@congrArg α β a b f h`, return `α`, `f` and `h`.
Also works if `e` can be turned into such an application (e.g. `congrFun`).
-/
def congrArg? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if e.isAppOfArity ``congrArg 6 then
    let #[α, _β, _a, _b, f, h] := e.getAppArgs | unreachable!
    return some (α, f, h)
  if e.isAppOfArity ``congrFun 6 then
    let #[α, β, _f, _g, h, a] := e.getAppArgs | unreachable!
    let α' ← withLocalDecl `x .default α fun x => do
      mkForallFVars #[x] (β.beta #[x])
    let f' ← withLocalDecl `x .default α' fun f => do
      mkLambdaFVars #[f] (f.app a)
    return some (α', f', h)
  return none

/-- Given `f : α → β` and `h : a = b`, returns a proof of `f a = f b`.-/
partial def mkCongrArg (f h : Expr) : MetaM Expr := do
  if let some a := isRefl? h then
    mkEqRefl (mkApp f a)
  else if let some (α, f₁, h₁) ← congrArg? h then
    -- Fuse nested `congrArg` for smaller proof terms, e.g. when using simp
    let f' ← withLocalDecl `x .default α fun x => do
      mkLambdaFVars #[x] (f.beta #[f₁.beta #[x]])
    mkCongrArg f' h₁
  else
    let hType ← infer h
    let fType ← infer f
    match fType.arrow?, hType.eq? with
    | some (α, β), some (_, a, b) =>
      let u ← getLevel α
      let v ← getLevel β
      return mkApp6 (mkConst ``congrArg [u, v]) α β a b f h
    | none, _ => throwAppBuilderException ``congrArg ("non-dependent function expected" ++ hasTypeMsg f fType)
    | _, none => throwAppBuilderException ``congrArg ("equality proof expected" ++ hasTypeMsg h hType)

/-- Given `h : f = g` and `a : α`, returns a proof of `f a = g a`.-/
def mkCongrFun (h a : Expr) : MetaM Expr := do
  if let some f := isRefl? h then
    mkEqRefl (mkApp f a)
  else if let some (α, f₁, h₁) ← congrArg? h then
    -- Fuse nested `congrArg` for smaller proof terms, e.g. when using simp
    let f' ← withLocalDecl `x .default α fun x => do
      mkLambdaFVars #[x] (f₁.beta #[x, a])
    mkCongrArg f' h₁
  else
    let hType ← infer h
    match hType.eq? with
    | some (ρ, f, g) => do
      let ρ ← whnfD ρ
      match ρ with
      | Expr.forallE n α β _ =>
        let β' := Lean.mkLambda n BinderInfo.default α β
        let u ← getLevel α
        let v ← getLevel (mkApp β' a)
        return mkApp6 (mkConst ``congrFun [u, v]) α β' f g h a
      | _ => throwAppBuilderException ``congrFun ("equality proof between functions expected" ++ hasTypeMsg h hType)
    | _ => throwAppBuilderException ``congrFun ("equality proof expected" ++ hasTypeMsg h hType)

/-- Given `h₁ : f = g` and `h₂ : a = b`, returns a proof of `f a = g b`. -/
def mkCongr (h₁ h₂ : Expr) : MetaM Expr := do
  if h₁.isAppOf ``Eq.refl then
    mkCongrArg h₁.appArg! h₂
  else if h₂.isAppOf ``Eq.refl then
    mkCongrFun h₁ h₂.appArg!
  else
    let hType₁ ← infer h₁
    let hType₂ ← infer h₂
    match hType₁.eq?, hType₂.eq? with
    | some (ρ, f, g), some (α, a, b) =>
      let ρ ← whnfD ρ
      match ρ.arrow? with
      | some (_, β) => do
        let u ← getLevel α
        let v ← getLevel β
        return mkApp8 (mkConst ``congr [u, v]) α β f g a b h₁ h₂
      | _ => throwAppBuilderException ``congr ("non-dependent function expected" ++ hasTypeMsg h₁ hType₁)
    | none, _ => throwAppBuilderException ``congr ("equality proof expected" ++ hasTypeMsg h₁ hType₁)
    | _, none => throwAppBuilderException ``congr ("equality proof expected" ++ hasTypeMsg h₂ hType₂)

private def mkAppMFinal (methodName : Name) (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← mvarId.getDecl
    let mvarVal  ← synthInstance mvarDecl.type
    mvarId.assign mvarVal
  let result ← instantiateMVars (mkAppN f args)
  if (← hasAssignableMVar result) then throwAppBuilderException methodName ("result contains metavariables" ++ indentExpr result)
  return result

private partial def mkAppMArgs (f : Expr) (fType : Expr) (xs : Array Expr) : MetaM Expr :=
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
    if h : i >= xs.size then
      mkAppMFinal `mkAppM f args instMVars
    else match type with
      | Expr.forallE n d b bi =>
        let d  := d.instantiateRevRange j args.size args
        match bi with
        | BinderInfo.implicit     =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) instMVars
        | BinderInfo.strictImplicit     =>
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
          throwAppBuilderException `mkAppM m!"too many explicit arguments provided to{indentExpr f}\narguments{indentD xs}"
  loop fType 0 0 #[] #[]

private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType ← instantiateTypeLevelParams cinfo us
  return (f, fType)

private def withAppBuilderTrace [ToMessageData α] [ToMessageData β]
    (f : α) (xs : β) (k : MetaM Expr) : MetaM Expr :=
  let emoji | .ok .. => checkEmoji | .error .. => crossEmoji
  withTraceNode `Meta.appBuilder (return m!"{emoji ·} f: {f}, xs: {xs}") do
    try
      let res ← k
      trace[Meta.appBuilder.result] res
      pure res
    catch ex =>
      trace[Meta.appBuilder.error] ex.toMessageData
      throw ex

/--
  Return the application `constName xs`.
  It tries to fill the implicit arguments before the last element in `xs`.

  Remark:
  ``mkAppM `arbitrary #[α]`` returns `@arbitrary.{u} α` without synthesizing
  the implicit argument occurring after `α`.
  Given a `x : ([Decidable p] → Bool) × Nat`, ``mkAppM `Prod.fst #[x]`` returns `@Prod.fst ([Decidable p] → Bool) Nat x`.
-/
def mkAppM (constName : Name) (xs : Array Expr) : MetaM Expr := do
  withAppBuilderTrace constName xs do withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    mkAppMArgs f fType xs

/-- Similar to `mkAppM`, but takes an `Expr` instead of a constant name. -/
def mkAppM' (f : Expr) (xs : Array Expr) : MetaM Expr := do
  let fType ← inferType f
  withAppBuilderTrace f xs do withNewMCtxDepth do
    mkAppMArgs f fType xs

private partial def mkAppOptMAux (f : Expr) (xs : Array (Option Expr)) : Nat → Array Expr → Nat → Array MVarId → Expr → MetaM Expr
  | i, args, j, instMVars, Expr.forallE n d b bi => do
    let d  := d.instantiateRevRange j args.size args
    if h : i < xs.size then
      match xs[i] with
      | none =>
        match bi with
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
  Given `Pure.pure {m : Type u → Type v} [Pure m] {α : Type u} (a : α) : m α`,
  ```
  mkAppOptM `Pure.pure #[m, none, none, a]
  ```
  returns a `Pure.pure` application if the instance `Pure m` can be synthesized, and the universe match.
  Note that,
  ```
  mkAppM `Pure.pure #[a]
  ```
  fails because the only explicit argument `(a : α)` is not sufficient for inferring the remaining arguments,
  we would need the expected type. -/
def mkAppOptM (constName : Name) (xs : Array (Option Expr)) : MetaM Expr := do
  withAppBuilderTrace constName xs do withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    mkAppOptMAux f xs 0 #[] 0 #[] fType

/-- Similar to `mkAppOptM`, but takes an `Expr` instead of a constant name. -/
def mkAppOptM' (f : Expr) (xs : Array (Option Expr)) : MetaM Expr := do
  let fType ← inferType f
  withAppBuilderTrace f xs do withNewMCtxDepth do
    mkAppOptMAux f xs 0 #[] 0 #[] fType

def mkEqNDRec (motive h1 h2 : Expr) : MetaM Expr := do
  if h2.isAppOf ``Eq.refl then
    return h1
  else
    let h2Type ← infer h2
    match h2Type.eq? with
    | none => throwAppBuilderException ``Eq.ndrec ("equality proof expected" ++ hasTypeMsg h2 h2Type)
    | some (α, a, b) =>
      let u2 ← getLevel α
      let motiveType ← infer motive
      match motiveType with
      | Expr.forallE _ _ (Expr.sort u1) _ =>
        return mkAppN (mkConst ``Eq.ndrec [u1, u2]) #[α, a, motive, h1, b, h2]
      | _ => throwAppBuilderException ``Eq.ndrec ("invalid motive" ++ indentExpr motive)

def mkEqRec (motive h1 h2 : Expr) : MetaM Expr := do
  if h2.isAppOf ``Eq.refl then
    return h1
  else
    let h2Type ← infer h2
    match h2Type.eq? with
    | none => throwAppBuilderException ``Eq.rec ("equality proof expected" ++ indentExpr h2)
    | some (α, a, b) =>
      let u2 ← getLevel α
      let motiveType ← infer motive
      match motiveType with
      | Expr.forallE _ _ (Expr.forallE _ _ (Expr.sort u1) _) _ =>
        return mkAppN (mkConst ``Eq.rec [u1, u2]) #[α, a, motive, h1, b, h2]
      | _ =>
        throwAppBuilderException ``Eq.rec ("invalid motive" ++ indentExpr motive)

def mkEqMP (eqProof pr : Expr) : MetaM Expr :=
  mkAppM ``Eq.mp #[eqProof, pr]

def mkEqMPR (eqProof pr : Expr) : MetaM Expr :=
  mkAppM ``Eq.mpr #[eqProof, pr]

def mkNoConfusion (target : Expr) (h : Expr) : MetaM Expr := do
  let type ← inferType h
  let type ← whnf type
  match type.eq? with
  | none           => throwAppBuilderException `noConfusion ("equality expected" ++ hasTypeMsg h type)
  | some (α, a, b) =>
    let α ← whnfD α
    matchConstInduct α.getAppFn (fun _ => throwAppBuilderException `noConfusion ("inductive type expected" ++ indentExpr α)) fun v us => do
      let u ← getLevel target
      return mkAppN (mkConst (Name.mkStr v.name "noConfusion") (u :: us)) (α.getAppArgs ++ #[target, a, b, h])

/-- Given a `monad` and `e : α`, makes `pure e`.-/
def mkPure (monad : Expr) (e : Expr) : MetaM Expr :=
  mkAppOptM ``Pure.pure #[monad, none, none, e]

/--
  `mkProjection s fieldName` returns an expression for accessing field `fieldName` of the structure `s`.
  Remark: `fieldName` may be a subfield of `s`. -/
partial def mkProjection (s : Expr) (fieldName : Name) : MetaM Expr := do
  let type ← inferType s
  let type ← whnf type
  match type.getAppFn with
  | Expr.const structName us =>
    let env ← getEnv
    unless isStructure env structName do
      throwAppBuilderException `mkProjection ("structure expected" ++ hasTypeMsg s type)
    match getProjFnForField? env structName fieldName with
    | some projFn =>
      let params := type.getAppArgs
      return mkApp (mkAppN (mkConst projFn us) params) s
    | none =>
      let fields := getStructureFields env structName
      let r? ← fields.findSomeM? fun fieldName' => do
        match isSubobjectField? env structName fieldName' with
        | none   => pure none
        | some _ =>
          let parent ← mkProjection s fieldName'
          (do let r ← mkProjection parent fieldName; return some r)
          <|>
          pure none
      match r? with
      | some r => pure r
      | none   => throwAppBuilderException `mkProjection ("invalid field name '" ++ toString fieldName ++ "' for" ++ hasTypeMsg s type)
  | _ => throwAppBuilderException `mkProjection ("structure expected" ++ hasTypeMsg s type)

private def mkListLitAux (nil : Expr) (cons : Expr) : List Expr → Expr
  | []    => nil
  | x::xs => mkApp (mkApp cons x) (mkListLitAux nil cons xs)

def mkListLit (type : Expr) (xs : List Expr) : MetaM Expr := do
  let u   ← getDecLevel type
  let nil := mkApp (mkConst ``List.nil [u]) type
  match xs with
  | [] => return nil
  | _  =>
    let cons := mkApp (mkConst ``List.cons [u]) type
    return mkListLitAux nil cons xs

def mkArrayLit (type : Expr) (xs : List Expr) : MetaM Expr := do
  let u ← getDecLevel type
  let listLit ← mkListLit type xs
  return mkApp (mkApp (mkConst ``List.toArray [u]) type) listLit

def mkNone (type : Expr) : MetaM Expr := do
  let u ← getDecLevel type
  return mkApp (mkConst ``Option.none [u]) type

def mkSome (type value : Expr) : MetaM Expr := do
  let u ← getDecLevel type
  return mkApp2 (mkConst ``Option.some [u]) type value

def mkSorry (type : Expr) (synthetic : Bool) : MetaM Expr := do
  let u ← getLevel type
  return mkApp2 (mkConst ``sorryAx [u]) type (toExpr synthetic)

/-- Return `Decidable.decide p` -/
def mkDecide (p : Expr) : MetaM Expr :=
  mkAppOptM ``Decidable.decide #[p, none]

/-- Return a proof for `p : Prop` using `decide p` -/
def mkDecideProof (p : Expr) : MetaM Expr := do
  let decP      ← mkDecide p
  let decEqTrue ← mkEq decP (mkConst ``Bool.true)
  let h         ← mkEqRefl (mkConst ``Bool.true)
  let h         ← mkExpectedTypeHint h decEqTrue
  mkAppM ``of_decide_eq_true #[h]

/-- Return `a < b` -/
def mkLt (a b : Expr) : MetaM Expr :=
  mkAppM ``LT.lt #[a, b]

/-- Return `a <= b` -/
def mkLe (a b : Expr) : MetaM Expr :=
  mkAppM ``LE.le #[a, b]

/-- Return `Inhabited.default α` -/
def mkDefault (α : Expr) : MetaM Expr :=
  mkAppOptM ``Inhabited.default #[α, none]

/-- Return `@Classical.ofNonempty α _` -/
def mkOfNonempty (α : Expr) : MetaM Expr := do
  mkAppOptM ``Classical.ofNonempty #[α, none]

/-- Return `sorryAx type` -/
def mkSyntheticSorry (type : Expr) : MetaM Expr :=
  return mkApp2 (mkConst ``sorryAx [← getLevel type]) type (mkConst ``Bool.true)

/-- Return `funext h` -/
def mkFunExt (h : Expr) : MetaM Expr :=
  mkAppM ``funext #[h]

/-- Return `propext h` -/
def mkPropExt (h : Expr) : MetaM Expr :=
  mkAppM ``propext #[h]

/-- Return `let_congr h₁ h₂` -/
def mkLetCongr (h₁ h₂ : Expr) : MetaM Expr :=
  mkAppM ``let_congr #[h₁, h₂]

/-- Return `let_val_congr b h` -/
def mkLetValCongr (b h : Expr) : MetaM Expr :=
  mkAppM ``let_val_congr #[b, h]

/-- Return `let_body_congr a h` -/
def mkLetBodyCongr (a h : Expr) : MetaM Expr :=
  mkAppM ``let_body_congr #[a, h]

/-- Return `of_eq_true h` -/
def mkOfEqTrue (h : Expr) : MetaM Expr :=
  mkAppM ``of_eq_true #[h]

/-- Return `eq_true h` -/
def mkEqTrue (h : Expr) : MetaM Expr :=
  mkAppM ``eq_true #[h]

/--
  Return `eq_false h`
  `h` must have type definitionally equal to `¬ p` in the current
  reducibility setting. -/
def mkEqFalse (h : Expr) : MetaM Expr :=
  mkAppM ``eq_false #[h]

/--
  Return `eq_false' h`
  `h` must have type definitionally equal to `p → False` in the current
  reducibility setting. -/
def mkEqFalse' (h : Expr) : MetaM Expr :=
  mkAppM ``eq_false' #[h]

def mkImpCongr (h₁ h₂ : Expr) : MetaM Expr :=
  mkAppM ``implies_congr #[h₁, h₂]

def mkImpCongrCtx (h₁ h₂ : Expr) : MetaM Expr :=
  mkAppM ``implies_congr_ctx #[h₁, h₂]

def mkImpDepCongrCtx (h₁ h₂ : Expr) : MetaM Expr :=
  mkAppM ``implies_dep_congr_ctx #[h₁, h₂]

def mkForallCongr (h : Expr) : MetaM Expr :=
  mkAppM ``forall_congr #[h]

/-- Return instance for `[Monad m]` if there is one -/
def isMonad? (m : Expr) : MetaM (Option Expr) :=
  try
    let monadType ← mkAppM `Monad #[m]
    let result    ← trySynthInstance monadType
    match result with
    | LOption.some inst => pure inst
    | _                 => pure none
  catch _ =>
    pure none

/-- Return `(n : type)`, a numeric literal of type `type`. The method fails if we don't have an instance `OfNat type n` -/
def mkNumeral (type : Expr) (n : Nat) : MetaM Expr := do
  let u ← getDecLevel type
  let inst ← synthInstance (mkApp2 (mkConst ``OfNat [u]) type (mkRawNatLit n))
  return mkApp3 (mkConst ``OfNat.ofNat [u]) type (mkRawNatLit n) inst

/--
  Return `a op b`, where `op` has name `opName` and is implemented using the typeclass `className`.
  This method assumes `a` and `b` have the same type, and typeclass `className` is heterogeneous.
  Examples of supported classes: `HAdd`, `HSub`, `HMul`.
  We use heterogeneous operators to ensure we have a uniform representation.
  -/
private def mkBinaryOp (className : Name) (opName : Name) (a b : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getDecLevel aType
  let inst ← synthInstance (mkApp3 (mkConst className [u, u, u]) aType aType aType)
  return mkApp6 (mkConst opName [u, u, u]) aType aType aType inst a b

/-- Return `a + b` using a heterogeneous `+`. This method assumes `a` and `b` have the same type. -/
def mkAdd (a b : Expr) : MetaM Expr := mkBinaryOp ``HAdd ``HAdd.hAdd a b

/-- Return `a - b` using a heterogeneous `-`. This method assumes `a` and `b` have the same type. -/
def mkSub (a b : Expr) : MetaM Expr := mkBinaryOp ``HSub ``HSub.hSub a b

/-- Return `a * b` using a heterogeneous `*`. This method assumes `a` and `b` have the same type. -/
def mkMul (a b : Expr) : MetaM Expr := mkBinaryOp ``HMul ``HMul.hMul a b

/--
  Return `a r b`, where `r` has name `rName` and is implemented using the typeclass `className`.
  This method assumes `a` and `b` have the same type.
  Examples of supported classes: `LE` and `LT`.
  We use heterogeneous operators to ensure we have a uniform representation.
  -/
private def mkBinaryRel (className : Name) (rName : Name) (a b : Expr) : MetaM Expr := do
  let aType ← inferType a
  let u ← getDecLevel aType
  let inst ← synthInstance (mkApp (mkConst className [u]) aType)
  return mkApp4 (mkConst rName [u]) aType inst a b

/-- Return `a ≤ b`. This method assumes `a` and `b` have the same type. -/
def mkLE (a b : Expr) : MetaM Expr := mkBinaryRel ``LE ``LE.le a b

/-- Return `a < b`. This method assumes `a` and `b` have the same type. -/
def mkLT (a b : Expr) : MetaM Expr := mkBinaryRel ``LT ``LT.lt a b

/-- Given `h : a = b`, return a proof for `a ↔ b`. -/
def mkIffOfEq (h : Expr) : MetaM Expr := do
  if h.isAppOfArity ``propext 3 then
    return h.appArg!
  else
    mkAppM ``Iff.of_eq #[h]

builtin_initialize do
  registerTraceClass `Meta.appBuilder
  registerTraceClass `Meta.appBuilder.result (inherited := true)
  registerTraceClass `Meta.appBuilder.error (inherited := true)

end Lean.Meta
