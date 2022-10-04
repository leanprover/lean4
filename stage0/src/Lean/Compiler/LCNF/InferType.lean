/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.PhaseExt

namespace Lean.Compiler.LCNF
/-! # Type inference for LCNF -/

/-
Note about **erasure confusion**.

1- After instantiating universe polymorphic code, we may have
some types that become propositions, and all propositions are erased.

For example, suppose we have
```
def f (α : Sort u) (x : α → α → Sort v) (a b : α) (h : x a b) ...
```
The LCNF type for this universe polymorphic declaration is
```
def f (α : Sort u) (x : α → α → Sort v) (a b : α) (h : x ◾ ◾) ...
```
Now, if we instantiate with `v` with the universe `0`, we have that `x ◾ ◾` is also a proposition
and should be erased.

2- We may also get "erasure confusion" when instantiating
polymorphic code with types and type formers. For example, suppose we have
```
structure S (α : Type u) (β : Type v) (f : α → β) where
  a : α
  b : β := f a
```
The LCNF type for `S.mk` is
```
S.mk : {α : Type u} → {β : Type v} → {f : α → β} → α → β → S α β ◾
```
Note that `f` was erased from the resulting type `S α β ◾` because it is
not a type former. Now, suppose we have the valid Lean declaration
```
def f : S Nat Type (fun _ => Nat) :=
 S.mk 0 Nat
```
The LNCF type for the value `S.mk 0 Nat` is `S Nat Type ◾` (see `S.mk` type above),
but the expected type is `S Nat Type (fun x => Nat)`. `fun x => Nat` is not erased
here because it is a type former.
-/

namespace InferType

/-
Type inference algorithm for LCNF. Invoked by the LCNF type checker
to check correctness of LCNF IR.
-/

/--
We use a regular local context to store temporary local declarations
created during type inference.
-/
abbrev InferTypeM := ReaderT LocalContext CompilerM

def getBinderName (fvarId : FVarId) : InferTypeM Name := do
  match (← read).find? fvarId with
  | some localDecl => return localDecl.userName
  | none => LCNF.getBinderName fvarId

def getType (fvarId : FVarId) : InferTypeM Expr := do
  match (← read).find? fvarId with
  | some localDecl => return localDecl.type
  | none => LCNF.getType fvarId

def mkForallFVars (xs : Array Expr) (type : Expr) : InferTypeM Expr :=
  let b := type.abstract xs
  xs.size.foldRevM (init := b) fun i b => do
    let x := xs[i]!
    let n ← InferType.getBinderName x.fvarId!
    let ty ← InferType.getType x.fvarId!
    let ty := ty.abstractRange i xs;
    return .forallE n ty b .default

def mkForallParams (params : Array Param) (type : Expr) : InferTypeM Expr :=
  let xs := params.map fun p => .fvar p.fvarId
  mkForallFVars xs type |>.run {}

@[inline] def withLocalDecl (binderName : Name) (type : Expr) (binderInfo : BinderInfo) (k : Expr → InferTypeM α) : InferTypeM α := do
  let fvarId ← mkFreshFVarId
  withReader (fun lctx => lctx.mkLocalDecl fvarId binderName type binderInfo) do
    k (.fvar fvarId)

def inferConstType (declName : Name) (us : List Level) : CompilerM Expr := do
  if declName == ``lcAny || declName == ``lcErased then
    return anyTypeExpr
  else if let some decl ← getDecl? declName then
    return decl.instantiateTypeLevelParams us
  else
    /-
    We need this case for declarations that do not have code associated with them.
    Example: constructors.
    TODO: phase support.
    -/
    instantiateLCNFTypeLevelParams declName us

mutual

  partial def inferType (e : Expr) : InferTypeM Expr :=
    match e with
    | .const c us    => inferConstType c us
    | .proj n i s    => inferProjType n i s
    | .app ..        => inferAppType e
    | .mvar ..       => throwError "unexpected metavariable {e}"
    | .fvar fvarId   => InferType.getType fvarId
    | .bvar ..       => throwError "unexpected bound variable {e}"
    | .mdata _ e     => inferType e
    | .lit v         => return v.type
    | .sort lvl      => return .sort (mkLevelSucc lvl)
    | .forallE ..    => inferForallType e
    | .lam ..        => inferLambdaType e
    | .letE ..       => inferLambdaType e

  partial def inferAppTypeCore (f : Expr) (args : Array Expr) : InferTypeM Expr := do
    let mut j := 0
    let mut fType ← inferType f
    for i in [:args.size] do
      fType := fType.headBeta
      match fType with
      | .forallE _ _ b _ => fType := b
      | _ =>
        fType := fType.instantiateRevRange j i args |>.headBeta
        match fType with
        | .forallE _ _ b _ => j := i; fType := b
        | _ =>
          if fType.isAnyType then return anyTypeExpr
          throwError "function expected{indentExpr (mkAppN f args[:i])} : {fType}\nfunction type{indentExpr (← inferType f)}"
    return fType.instantiateRevRange j args.size args |>.headBeta

  partial def inferAppType (e : Expr) : InferTypeM Expr := do
    inferAppTypeCore e.getAppFn e.getAppArgs

  partial def inferProjType (structName : Name) (idx : Nat) (s : Expr) : InferTypeM Expr := do
    let failed {α} : Unit → InferTypeM α := fun _ =>
      throwError "invalid projection{indentExpr (mkProj structName idx s)}"
    let structType := (← inferType s).headBeta
    if structType.isAnyType then
      /- TODO: after we erase universe variables, we can just extract a better type using just `structName` and `idx`. -/
      return anyTypeExpr
    else
      matchConstStruct structType.getAppFn failed fun structVal structLvls ctorVal =>
        let n := structVal.numParams
        let structParams := structType.getAppArgs
        if n != structParams.size then
          failed ()
        else do
          let mut ctorType ← inferAppType (mkAppN (mkConst ctorVal.name structLvls) structParams)
          for _ in [:idx] do
            match ctorType with
            | .forallE _ _ body _ =>
              if body.hasLooseBVars then
                -- This can happen when one of the fields is a type or type former.
                ctorType := body.instantiate1 anyTypeExpr
              else
                ctorType := body
            | _ =>
              if ctorType.isAnyType then return anyTypeExpr
              failed ()
          match ctorType with
          | .forallE _ d _ _ => return d
          | _ =>
            if ctorType.isAnyType then return anyTypeExpr
            failed ()

  partial def getLevel? (type : Expr) : InferTypeM (Option Level) := do
    match (← inferType type) with
    | .sort u => return some u
    | e =>
      if e.isAnyType then
        return none
      else
        throwError "type expected{indentExpr type}"

  partial def inferForallType (e : Expr) : InferTypeM Expr :=
    go e #[]
  where
    go (e : Expr) (fvars : Array Expr) : InferTypeM Expr := do
      match e with
      | .forallE n d b bi =>
        withLocalDecl n (d.instantiateRev fvars) bi fun fvar =>
          go b (fvars.push fvar)
      | _ =>
        let e := e.instantiateRev fvars
        let some u ← getLevel? e | return anyTypeExpr
        let mut u := u
        for x in fvars.reverse do
          let xType ← inferType x
          let some v ← getLevel? xType | return anyTypeExpr
          u := mkLevelIMax' v u
        return .sort u.normalize

  partial def inferLambdaType (e : Expr) : InferTypeM Expr :=
    go e #[] #[]
  where
    go (e : Expr) (fvars : Array Expr) (all : Array Expr) : InferTypeM Expr := do
      match e with
      | .lam n d b bi =>
        withLocalDecl n (d.instantiateRev all) bi fun fvar => go b (fvars.push fvar) (all.push fvar)
      | .letE n t _ b _ =>
        withLocalDecl n (t.instantiateRev all) .default fun fvar => go b fvars (all.push fvar)
      | e =>
        let type ← inferType (e.instantiateRev all)
        mkForallFVars fvars type

end
end InferType

def inferType (e : Expr) : CompilerM Expr :=
  InferType.inferType e |>.run {}

def getLevel (type : Expr) : CompilerM Level := do
  match (← inferType type) with
  | .sort u => return u
  | e => if e.isAnyType then return levelOne else throwError "type expected{indentExpr type}"

/-- Create `lcCast expectedType e : expectedType` -/
def mkLcCast (e : Expr) (expectedType : Expr) : CompilerM Expr := do
  let type ← inferType e
  let u ← getLevel type
  let v ← getLevel expectedType
  return mkApp3 (.const ``lcCast [u, v]) type expectedType e

def Code.inferType (code : Code) : CompilerM Expr := do
  match code with
  | .let _ k | .fun _ k | .jp _ k => k.inferType
  | .return fvarId => getType fvarId
  | .jmp fvarId args => InferType.inferAppTypeCore (.fvar fvarId) args |>.run {}
  | .unreach type => return type
  | .cases c => return c.resultType

def Code.inferParamType (params : Array Param) (code : Code) : CompilerM Expr := do
  let type ← code.inferType
  let xs := params.map fun p => .fvar p.fvarId
  InferType.mkForallFVars xs type |>.run {}

def AltCore.inferType (alt : Alt) : CompilerM Expr :=
  alt.getCode.inferType

def mkAuxLetDecl (e : Expr) (prefixName := `_x) : CompilerM LetDecl := do
  mkLetDecl (← mkFreshBinderName prefixName) (← inferType e) e

def mkForallParams (params : Array Param) (type : Expr) : CompilerM Expr :=
  InferType.mkForallParams params type |>.run {}

def mkAuxFunDecl (params : Array Param) (code : Code) (prefixName := `_f) : CompilerM FunDecl := do
  let type ← mkForallParams params (← code.inferType)
  let binderName ← mkFreshBinderName prefixName
  mkFunDecl binderName type params code

def mkAuxJpDecl (params : Array Param) (code : Code) (prefixName := `_jp) : CompilerM FunDecl := do
  mkAuxFunDecl params code prefixName

def mkAuxJpDecl' (param : Param) (code : Code) (prefixName := `_jp) : CompilerM FunDecl := do
  let params := #[param]
  mkAuxFunDecl params code prefixName

def instantiateForall (type : Expr) (params : Array Param) : CoreM Expr :=
  go type 0
where
  go (type : Expr) (i : Nat) : CoreM Expr :=
    if h : i < params.size then
      let p := params[i]
      match type.headBeta with
      | .forallE _ _ b _ => go (b.instantiate1 (.fvar p.fvarId)) (i+1)
      | _ => throwError "invalid instantiateForall, too many parameters"
    else
      return type
termination_by go i => params.size - i

def mkCasesResultType (alts : Array Alt) : CompilerM Expr := do
  if alts.isEmpty then
    throwError "`Code.bind` failed, empty `cases` found"
  let mut resultType ← alts[0]!.inferType
  for alt in alts[1:] do
    resultType := joinTypes resultType (← alt.inferType)
  return resultType

/--
Return `true` if `type` should be erased. See item 1 in the note above where `x ◾ ◾` is
a proposition and should be erased when the universe level parameter is set to 0.

Remark: `predVars` is a bitmask that indicates whether de-bruijn variables are predicates or not.
That is, `#i` is a predicate if `predVars[predVars.size - i - 1] = true`
-/
partial def isErasedCompatible (type : Expr) (predVars : Array Bool := #[]): CompilerM Bool :=
  go type predVars
where
  go (type : Expr) (predVars : Array Bool) : CompilerM Bool := do
    let type := type.headBeta
    match type with
    | .const ..        => return type.isErased
    | .sort ..         => return false
    | .mdata _ e       => go e predVars
    | .forallE _ t b _
    | .lam _ t b _     => go b (predVars.push <| isPredicateType t)
    | .app f _         => go f predVars
    | .bvar idx        => return predVars[predVars.size - idx - 1]!
    | .fvar fvarId     => return isPredicateType (← getType fvarId)
    | .proj .. | .mvar .. | .letE .. | .lit .. => unreachable!

/--
Quick check for `compatibleTypes`. It is not monadic, but it is incomplete
because it does not eta-expand type formers. See comment at `compatibleTypes`.

Remark: if the result is `true`, then `a` and `b` are indeed compatible.
If it is `false`, we must use the full-check.
-/
partial def compatibleTypesQuick (a b : Expr) : Bool :=
  if a.isAnyType || b.isAnyType then
    true
  else if a.isErased || b.isErased then
    true
  else
    let a' := a.headBeta
    let b' := b.headBeta
    if a != a' || b != b' then
      compatibleTypesQuick a' b'
    else if a == b then
      true
    else
      match a, b with
      | .mdata _ a, b => compatibleTypesQuick a b
      | a, .mdata _ b => compatibleTypesQuick a b
      -- Note that even after reducing to head-beta, we can still have `.app` terms. For example,
      -- an inductive constructor application such as `List Int`
      | .app f a, .app g b => compatibleTypesQuick f g && compatibleTypesQuick a b
      | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => compatibleTypesQuick d₁ d₂ && compatibleTypesQuick b₁ b₂
      | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ => compatibleTypesQuick d₁ d₂ && compatibleTypesQuick b₁ b₂
      | .sort u, .sort v => Level.isEquiv u v
      | .const n us, .const m vs => n == m && List.isEqv us vs Level.isEquiv
      | _, _ => false

/--
Complete check for `compatibleTypes`. It eta-expands type formers. See comment at `compatibleTypes`.
-/
partial def InferType.compatibleTypesFull (a b : Expr) : InferTypeM Bool := do
  if a.isAnyType || b.isAnyType then
    return true
  else if a.isErased || b.isErased then
    return true
  else
    let a' := a.headBeta
    let b' := b.headBeta
    if a != a' || b != b' then
      compatibleTypesFull a' b'
    else if a == b then
      return true
    else
      match a, b with
      | .mdata _ a, b => compatibleTypesFull a b
      | a, .mdata _ b => compatibleTypesFull a b
      -- Note that even after reducing to head-beta, we can still have `.app` terms. For example,
      -- an inductive constructor application such as `List Int`
      | .app f a, .app g b => compatibleTypesFull f g <&&> compatibleTypesFull a b
      | .forallE n d₁ b₁ bi, .forallE _ d₂ b₂ _ =>
        unless (← compatibleTypesFull d₁ d₂) do return false
        withLocalDecl n d₁ bi fun x =>
          compatibleTypesFull (b₁.instantiate1 x) (b₂.instantiate1 x)
      | .lam n d₁ b₁ bi, .lam _ d₂ b₂ _ =>
        unless (← compatibleTypesFull d₁ d₂) do return false
        withLocalDecl n d₁ bi fun x =>
          compatibleTypesFull (b₁.instantiate1 x) (b₂.instantiate1 x)
      | .sort u, .sort v => return Level.isEquiv u v
      | .const n us, .const m vs => return n == m && List.isEqv us vs Level.isEquiv
      | _, _ =>
        if a.isLambda then
          let some b ← etaExpand? b | return false
          compatibleTypesFull a b
        else if b.isLambda then
          let some a ← etaExpand? a | return false
          compatibleTypesFull a b
        else
          return false
where
  etaExpand? (e : Expr) : InferTypeM (Option Expr) := do
    match (← inferType e).headBeta with
    | .forallE n d _ bi =>
      /-
      In principle, `.app e (.bvar 0)` may not be a valid LCNF type sub-expression
      because `d` may not be a type former type, See remark `compatibleTypes` for
      a justification why this is ok.
      -/
      return some (.lam n d (.app e (.bvar 0)) bi)
    | _ => return none

/--
Return true if the LCNF types `a` and `b` are compatible.

Remark: `a` and `b` can be type formers (e.g., `List`, or `fun (α : Type) => Nat → Nat × α`)

Remark: We may need to eta-expand type formers to establish whether they are compatible or not.
For example, suppose we have
```
fun (x : B) => Id B ◾ ◾
Id B ◾
```
We must eta-expand `Id B ◾` to `fun (x : B) => Id B ◾ x`. Note that, we use `x` instead of `◾` to
make the implementation simpler and skip the check whether `B` is a type former type. However,
this simplification should not affect correctness since `◾` is compatible with everything.

Remark: see comment at `isErasedCompatible`.

Remark: because of "erasure confusion" see note above, we assume `◾` (aka `lcErasure`) is compatible with everything.
This is a simplification. We used to use `isErasedCompatible`, but this only address item 1.
For item 2, we would have to modify the `toLCNFType` function and make sure a type former is erased if the expected
type is not always a type former (see `S.mk` type and example in the note above).
-/
def InferType.compatibleTypes (a b : Expr) : InferTypeM Bool := do
  if compatibleTypesQuick a b then
    return true
  else
    compatibleTypesFull a b

@[inheritDoc InferType.compatibleTypes]
def compatibleTypes (a b : Expr) : CompilerM Bool :=
  if compatibleTypesQuick a b then
    return true
  else
    InferType.compatibleTypesFull a b |>.run {}

end Lean.Compiler.LCNF
