/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.OtherDecl

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
  xs.size.foldRevM (init := b) fun i _ b => do
    let x := xs[i]
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
  if declName == ``lcErased then
    return erasedExpr
  else if let some decl ← getDecl? declName then
    return decl.instantiateTypeLevelParams us
  else
    /- Declaration does not have code associated with it: constructor, inductive type, foreign function -/
    getOtherDeclType declName us

def inferLitValueType (value : LitValue) : Expr :=
  match value with
  | .natVal .. => mkConst ``Nat
  | .strVal .. => mkConst ``String

mutual
  partial def inferArgType (arg : Arg) : InferTypeM Expr :=
    match arg with
    | .erased => return erasedExpr
    | .type e => inferType e
    | .fvar fvarId => LCNF.getType fvarId

  partial def inferType (e : Expr) : InferTypeM Expr :=
    match e with
    | .const c us    => inferConstType c us
    | .app ..        => inferAppType e
    | .fvar fvarId   => InferType.getType fvarId
    | .sort lvl      => return .sort (mkLevelSucc lvl)
    | .forallE ..    => inferForallType e
    | .lam ..        => inferLambdaType e
    | .letE .. | .mvar .. | .mdata .. | .lit .. | .bvar .. | .proj .. => unreachable!

  partial def inferLetValueType (e : LetValue) : InferTypeM Expr := do
    match e with
    | .erased => return erasedExpr
    | .value v => return inferLitValueType v
    | .proj structName idx fvarId => inferProjType structName idx fvarId
    | .const declName us args => inferAppTypeCore (← inferConstType declName us) args
    | .fvar fvarId args => inferAppTypeCore (← getType fvarId) args

  partial def inferAppTypeCore (fType : Expr) (args : Array Arg) : InferTypeM Expr := do
    let mut j := 0
    let mut fType := fType
    for i in [:args.size] do
      fType := fType.headBeta
      match fType with
      | .forallE _ _ b _ => fType := b
      | _ =>
        fType := instantiateRevRangeArgs fType j i args |>.headBeta
        match fType with
        | .forallE _ _ b _ => j := i; fType := b
        | _ => return erasedExpr
    return instantiateRevRangeArgs fType j args.size args |>.headBeta

  partial def inferAppType (e : Expr) : InferTypeM Expr := do
    let mut j := 0
    let mut fType ← inferType e.getAppFn
    let args := e.getAppArgs
    for i in [:args.size] do
      fType := fType.headBeta
      match fType with
      | .forallE _ _ b _ => fType := b
      | _ =>
        fType := fType.instantiateRevRange j i args |>.headBeta
        match fType with
        | .forallE _ _ b _ => j := i; fType := b
        | _ => return erasedExpr
    return fType.instantiateRevRange j args.size args |>.headBeta

  partial def inferProjType (structName : Name) (idx : Nat) (s : FVarId) : InferTypeM Expr := do
    let failed {α} : Unit → InferTypeM α := fun _ =>
      throwError "invalid projection{indentExpr (mkProj structName idx (mkFVar s))}"
    let structType := (← getType s).headBeta
    if structType.isErased then
      /- TODO: after we erase universe variables, we can just extract a better type using just `structName` and `idx`. -/
      return erasedExpr
    else
      matchConstStructure structType.getAppFn failed fun structVal structLvls ctorVal =>
        let structTypeArgs := structType.getAppArgs
        if structVal.numParams + structVal.numIndices != structTypeArgs.size then
          failed ()
        else do
          let mut ctorType ← inferAppType (mkAppN (mkConst ctorVal.name structLvls) structTypeArgs[:structVal.numParams])
          for _ in [:idx] do
            match ctorType with
            | .forallE _ _ body _ =>
              if body.hasLooseBVars then
                -- This can happen when one of the fields is a type or type former.
                ctorType := body.instantiate1 erasedExpr
              else
                ctorType := body
            | _ =>
              if ctorType.isErased then return erasedExpr
              failed ()
          match ctorType with
          | .forallE _ d _ _ => return d
          | _ =>
            if ctorType.isErased then return erasedExpr
            failed ()

  partial def getLevel? (type : Expr) : InferTypeM (Option Level) := do
    match (← inferType type) with
    | .sort u => return some u
    | _ => return none

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
        let some u ← getLevel? e | return erasedExpr
        let mut u := u
        for x in fvars.reverse do
          let xType ← inferType x
          let some v ← getLevel? xType | return erasedExpr
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

def inferAppType (fnType : Expr) (args : Array Arg) : CompilerM Expr :=
  InferType.inferAppTypeCore fnType args |>.run {}

def getLevel (type : Expr) : CompilerM Level := do
  match (← inferType type) with
  | .sort u => return u
  | e => if e.isErased then return levelOne else throwError "type expected{indentExpr type}"

def Arg.inferType (arg : Arg) : CompilerM Expr :=
  InferType.inferArgType arg |>.run {}

def LetValue.inferType (e : LetValue) : CompilerM Expr :=
  InferType.inferLetValueType e |>.run {}

def Code.inferType (code : Code) : CompilerM Expr := do
  match code with
  | .let _ k | .fun _ k | .jp _ k => k.inferType
  | .return fvarId => getType fvarId
  | .jmp fvarId args => InferType.inferAppTypeCore (← getType fvarId) args |>.run {}
  | .unreach type => return type
  | .cases c => return c.resultType

def Code.inferParamType (params : Array Param) (code : Code) : CompilerM Expr := do
  let type ← code.inferType
  let xs := params.map fun p => .fvar p.fvarId
  InferType.mkForallFVars xs type |>.run {}

def AltCore.inferType (alt : Alt) : CompilerM Expr :=
  alt.getCode.inferType

def mkAuxLetDecl (e : LetValue) (prefixName := `_x) : CompilerM LetDecl := do
  mkLetDecl (← mkFreshBinderName prefixName) (← e.inferType) e

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
Return `true` if the given LCNF are equivalent.
`List Nat` and `(fun x => List x) Nat` are both equivalent.
-/
partial def eqvTypes (a b : Expr) : Bool :=
  if a == b then
    true
  else if a.isErased && b.isErased then
    -- `◾ α` is equivalent to `◾`
    true
  else
    let a' := a.headBeta
    let b' := b.headBeta
    if a != a' || b != b' then
      eqvTypes a' b'
    else
      match a, b with
      | .mdata _ a, b => eqvTypes a b
      | a, .mdata _ b => eqvTypes a b
      | .app f a, .app g b => eqvTypes f g && eqvTypes a b
      | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => eqvTypes d₁ d₂ && eqvTypes b₁ b₂
      | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ => eqvTypes d₁ d₂ && eqvTypes b₁ b₂
      | .sort u, .sort v => Level.isEquiv u v
      | .const n us, .const m vs => n == m && List.isEqv us vs Level.isEquiv
      | _, _ => false

end Lean.Compiler.LCNF
