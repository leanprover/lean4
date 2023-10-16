/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Meta.Instances
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.Types

namespace Lean.Compiler.LCNF

/-!
# Lean Compiler Normal Form (LCNF)

It is based on the [A-normal form](https://en.wikipedia.org/wiki/A-normal_form),
and the approach described in the paper
[Compiling  without continuations](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/compiling-without-continuations.pdf).

-/

structure Param where
  fvarId     : FVarId
  binderName : Name
  type       : Expr
  borrow     : Bool
  deriving Inhabited, BEq

def Param.toExpr (p : Param) : Expr :=
  .fvar p.fvarId

inductive AltCore (Code : Type) where
  | alt (ctorName : Name) (params : Array Param) (code : Code)
  | default (code : Code)
  deriving Inhabited

inductive LitValue where
  | natVal (val : Nat)
  | strVal (val : String)
  -- TODO: add constructors for `Int`, `Float`, `UInt` ...
  deriving Inhabited, BEq, Hashable

def LitValue.toExpr : LitValue → Expr
  | .natVal v => .lit (.natVal v)
  | .strVal v => .lit (.strVal v)

inductive Arg where
  | erased
  | fvar (fvarId : FVarId)
  | type (expr : Expr)
  deriving Inhabited, BEq, Hashable

def Param.toArg (p : Param) : Arg :=
  .fvar p.fvarId

def Arg.toExpr (arg : Arg) : Expr :=
  match arg with
  | .erased => erasedExpr
  | .fvar fvarId => .fvar fvarId
  | .type e => e

private unsafe def Arg.updateTypeImp (arg : Arg) (type' : Expr) : Arg :=
  match arg with
  | .type ty => if ptrEq ty type' then arg else .type type'
  | _ => unreachable!

@[implemented_by Arg.updateTypeImp] opaque Arg.updateType! (arg : Arg) (type : Expr) : Arg

private unsafe def Arg.updateFVarImp (arg : Arg) (fvarId' : FVarId) : Arg :=
  match arg with
  | .fvar fvarId => if fvarId' == fvarId then arg else .fvar fvarId'
  | _ => unreachable!

@[implemented_by Arg.updateFVarImp] opaque Arg.updateFVar! (arg : Arg) (fvarId' : FVarId) : Arg

inductive LetValue where
  | value (value : LitValue)
  | erased
  | proj (typeName : Name) (idx : Nat) (struct : FVarId)
  | const (declName : Name) (us : List Level) (args : Array Arg)
  | fvar (fvarId : FVarId) (args : Array Arg)
  -- TODO: add constructors for mono and impure phases
  deriving Inhabited, BEq, Hashable

def Arg.toLetValue (arg : Arg) : LetValue :=
  match arg with
  | .fvar fvarId => .fvar fvarId #[]
  | .erased | .type .. => .erased

private unsafe def LetValue.updateProjImp (e : LetValue) (fvarId' : FVarId) : LetValue :=
  match e with
  | .proj s i fvarId => if fvarId == fvarId' then e else .proj s i fvarId'
  | _ => unreachable!

@[implemented_by LetValue.updateProjImp] opaque LetValue.updateProj! (e : LetValue) (fvarId' : FVarId) : LetValue

private unsafe def LetValue.updateConstImp (e : LetValue) (declName' : Name) (us' : List Level) (args' : Array Arg) : LetValue :=
  match e with
  | .const declName us args => if declName == declName' && ptrEq us us' && ptrEq args args' then e else .const declName' us' args'
  | _ => unreachable!

@[implemented_by LetValue.updateConstImp] opaque LetValue.updateConst! (e : LetValue) (declName' : Name) (us' : List Level) (args' : Array Arg) : LetValue

private unsafe def LetValue.updateFVarImp (e : LetValue) (fvarId' : FVarId) (args' : Array Arg) : LetValue :=
  match e with
  | .fvar fvarId args => if fvarId == fvarId' && ptrEq args args' then e else .fvar fvarId' args'
  | _ => unreachable!

@[implemented_by LetValue.updateFVarImp] opaque LetValue.updateFVar! (e : LetValue) (fvarId' : FVarId) (args' : Array Arg) : LetValue

private unsafe def LetValue.updateArgsImp (e : LetValue) (args' : Array Arg) : LetValue :=
  match e with
  | .const declName us args => if ptrEq args args' then e else .const declName us args'
  | .fvar fvarId args => if ptrEq args args' then e else .fvar fvarId args'
  | _ => unreachable!

@[implemented_by LetValue.updateArgsImp] opaque LetValue.updateArgs! (e : LetValue) (args' : Array Arg) : LetValue

def LetValue.toExpr (e : LetValue) : Expr :=
  match e with
  | .value (.natVal val) => .lit (.natVal val)
  | .value (.strVal val) => .lit (.strVal val)
  | .erased => erasedExpr
  | .proj n i s => .proj n i (.fvar s)
  | .const n us as => mkAppN (.const n us) (as.map Arg.toExpr)
  | .fvar fvarId as => mkAppN (.fvar fvarId) (as.map Arg.toExpr)

structure LetDecl where
  fvarId : FVarId
  binderName : Name
  type : Expr
  value : LetValue
  deriving Inhabited, BEq

structure FunDeclCore (Code : Type) where
  fvarId : FVarId
  binderName : Name
  params : Array Param
  type : Expr
  value : Code
  deriving Inhabited

def FunDeclCore.getArity (decl : FunDeclCore Code) : Nat :=
  decl.params.size

structure CasesCore (Code : Type) where
  typeName : Name
  resultType : Expr
  discr : FVarId
  alts : Array (AltCore Code)
  deriving Inhabited

inductive Code where
  | let (decl : LetDecl) (k : Code)
  | fun (decl : FunDeclCore Code) (k : Code)
  | jp (decl : FunDeclCore Code) (k : Code)
  | jmp (fvarId : FVarId) (args : Array Arg)
  | cases (cases : CasesCore Code)
  | return (fvarId : FVarId)
  | unreach (type : Expr)
  deriving Inhabited

abbrev Alt := AltCore Code
abbrev FunDecl := FunDeclCore Code
abbrev Cases := CasesCore Code

/--
Return the constructor names that have an explicit (non-default) alternative.
-/
def CasesCore.getCtorNames (c : Cases) : NameSet :=
  c.alts.foldl (init := {}) fun ctorNames alt =>
    match alt with
    | .default _ => ctorNames
    | .alt ctorName .. => ctorNames.insert ctorName

inductive CodeDecl where
  | let (decl : LetDecl)
  | fun (decl : FunDecl)
  | jp (decl : FunDecl)
  deriving Inhabited

def CodeDecl.fvarId : CodeDecl → FVarId
  | .let decl | .fun decl | .jp decl => decl.fvarId

def attachCodeDecls (decls : Array CodeDecl) (code : Code) : Code :=
  go decls.size code
where
  go (i : Nat) (code : Code) : Code :=
    if i > 0 then
      match decls[i-1]! with
      | .let decl => go (i-1) (.let decl code)
      | .fun decl => go (i-1) (.fun decl code)
      | .jp decl => go (i-1) (.jp decl code)
    else
      code

mutual
  private unsafe def eqImp (c₁ c₂ : Code) : Bool :=
    if ptrEq c₁ c₂ then
      true
    else match c₁, c₂ with
      | .let d₁ k₁, .let d₂ k₂ => d₁ == d₂ && eqImp k₁ k₂
      | .fun d₁ k₁, .fun d₂ k₂
      | .jp d₁ k₁, .jp d₂ k₂ => eqFunDecl d₁ d₂ && eqImp k₁ k₂
      | .cases c₁, .cases c₂ => eqCases c₁ c₂
      | .jmp j₁ as₁, .jmp j₂ as₂ => j₁ == j₂ && as₁ == as₂
      | .return r₁, .return r₂ => r₁ == r₂
      | .unreach t₁, .unreach t₂ => t₁ == t₂
      | _, _ => false

  private unsafe def eqFunDecl (d₁ d₂ : FunDecl) : Bool :=
    if ptrEq d₁ d₂ then
      true
    else
      d₁.fvarId == d₂.fvarId && d₁.binderName == d₂.binderName &&
      d₁.params == d₂.params && d₁.type == d₂.type &&
      eqImp d₁.value d₂.value

  private unsafe def eqCases (c₁ c₂ : Cases) : Bool :=
    c₁.resultType == c₂.resultType && c₁.discr == c₂.discr &&
    c₁.typeName == c₂.typeName && c₁.alts.isEqv c₂.alts eqAlt

  private unsafe def eqAlt (a₁ a₂ : Alt) : Bool :=
    match a₁, a₂ with
    | .default k₁, .default k₂ => eqImp k₁ k₂
    | .alt c₁ ps₁ k₁, .alt c₂ ps₂ k₂ => c₁ == c₂ && ps₁ == ps₂ && eqImp k₁ k₂
    | _, _ => false
end

@[implemented_by eqImp] protected opaque Code.beq : Code → Code → Bool

instance : BEq Code where
  beq := Code.beq

@[implemented_by eqFunDecl] protected opaque FunDecl.beq : FunDecl → FunDecl → Bool

instance : BEq FunDecl where
  beq := FunDecl.beq

def AltCore.getCode : Alt → Code
  | .default k => k
  | .alt _ _ k => k

def AltCore.getParams : Alt → Array Param
  | .default _ => #[]
  | .alt _ ps _ => ps

def AltCore.forCodeM [Monad m] (alt : Alt) (f : Code → m Unit) : m Unit := do
  match alt with
  | .default k => f k
  | .alt _ _ k => f k

private unsafe def updateAltCodeImp (alt : Alt) (k' : Code) : Alt :=
  match alt with
  | .default k => if ptrEq k k' then alt else .default k'
  | .alt ctorName ps k => if ptrEq k k' then alt else .alt ctorName ps k'

@[implemented_by updateAltCodeImp] opaque AltCore.updateCode (alt : Alt) (c : Code) : Alt

private unsafe def updateAltImp (alt : Alt) (ps' : Array Param) (k' : Code) : Alt :=
  match alt with
  | .alt ctorName ps k => if ptrEq k k' && ptrEq ps ps' then alt else .alt ctorName ps' k'
  | _ => unreachable!

@[implemented_by updateAltImp] opaque AltCore.updateAlt! (alt : Alt) (ps' : Array Param) (k' : Code) : Alt

@[inline] private unsafe def updateAltsImp (c : Code) (alts : Array Alt) : Code :=
  match c with
  | .cases cs => if ptrEq cs.alts alts then c else .cases { cs with alts }
  | _ => unreachable!

@[implemented_by updateAltsImp] opaque Code.updateAlts! (c : Code) (alts : Array Alt) : Code

@[inline] private unsafe def updateCasesImp (c : Code) (resultType : Expr) (discr : FVarId) (alts : Array Alt) : Code :=
  match c with
  | .cases cs => if ptrEq cs.alts alts && ptrEq cs.resultType resultType && cs.discr == discr then c else .cases { cs with discr, resultType, alts }
  | _ => unreachable!

@[implemented_by updateCasesImp] opaque Code.updateCases! (c : Code) (resultType : Expr) (discr : FVarId) (alts : Array Alt) : Code

@[inline] private unsafe def updateLetImp (c : Code) (decl' : LetDecl) (k' : Code) : Code :=
  match c with
  | .let decl k => if ptrEq k k' && ptrEq decl decl' then c else .let decl' k'
  | _ => unreachable!

@[implemented_by updateLetImp] opaque Code.updateLet! (c : Code) (decl' : LetDecl) (k' : Code) : Code

@[inline] private unsafe def updateContImp (c : Code) (k' : Code) : Code :=
  match c with
  | .let decl k => if ptrEq k k' then c else .let decl k'
  | .fun decl k => if ptrEq k k' then c else .fun decl k'
  | .jp decl k => if ptrEq k k' then c else .jp decl k'
  | _ => unreachable!

@[implemented_by updateContImp] opaque Code.updateCont! (c : Code) (k' : Code) : Code

@[inline] private unsafe def updateFunImp (c : Code) (decl' : FunDecl) (k' : Code) : Code :=
  match c with
  | .fun decl k => if ptrEq k k' && ptrEq decl decl' then c else .fun decl' k'
  | .jp decl k => if ptrEq k k' && ptrEq decl decl' then c else .jp decl' k'
  | _ => unreachable!

@[implemented_by updateFunImp] opaque Code.updateFun! (c : Code) (decl' : FunDecl) (k' : Code) : Code

@[inline] private unsafe def updateReturnImp (c : Code) (fvarId' : FVarId) : Code :=
  match c with
  | .return fvarId => if fvarId == fvarId' then c else .return fvarId'
  | _ => unreachable!

@[implemented_by updateReturnImp] opaque Code.updateReturn! (c : Code) (fvarId' : FVarId) : Code

@[inline] private unsafe def updateJmpImp (c : Code) (fvarId' : FVarId) (args' : Array Arg) : Code :=
  match c with
  | .jmp fvarId args => if fvarId == fvarId' && ptrEq args args' then c else .jmp fvarId' args'
  | _ => unreachable!

@[implemented_by updateJmpImp] opaque Code.updateJmp! (c : Code) (fvarId' : FVarId) (args' : Array Arg) : Code

@[inline] private unsafe def updateUnreachImp (c : Code) (type' : Expr) : Code :=
  match c with
  | .unreach type => if ptrEq type type' then c else .unreach type'
  | _ => unreachable!

@[implemented_by updateUnreachImp] opaque Code.updateUnreach! (c : Code) (type' : Expr) : Code

private unsafe def updateParamCoreImp (p : Param) (type : Expr) : Param :=
  if ptrEq type p.type then
    p
  else
    { p with type }

/--
Low-level update `Param` function. It does not update the local context.
Consider using `Param.update : Param → Expr → CompilerM Param` if you want the local context
to be updated.
-/
@[implemented_by updateParamCoreImp] opaque Param.updateCore (p : Param) (type : Expr) : Param

private unsafe def updateLetDeclCoreImp (decl : LetDecl) (type : Expr) (value : LetValue) : LetDecl :=
  if ptrEq type decl.type && ptrEq value decl.value then
    decl
  else
    { decl with type, value }

/--
Low-level update `LetDecl` function. It does not update the local context.
Consider using `LetDecl.update : LetDecl → Expr → Expr → CompilerM LetDecl` if you want the local context
to be updated.
-/
@[implemented_by updateLetDeclCoreImp] opaque LetDecl.updateCore (decl : LetDecl) (type : Expr) (value : LetValue) : LetDecl

private unsafe def updateFunDeclCoreImp (decl: FunDecl) (type : Expr) (params : Array Param) (value : Code) : FunDecl :=
  if ptrEq type decl.type && ptrEq params decl.params && ptrEq value decl.value then
    decl
  else
    { decl with type, params, value }

/--
Low-level update `FunDecl` function. It does not update the local context.
Consider using `FunDecl.update : LetDecl → Expr → Array Param → Code → CompilerM FunDecl` if you want the local context
to be updated.
-/
@[implemented_by updateFunDeclCoreImp] opaque FunDeclCore.updateCore (decl: FunDecl) (type : Expr) (params : Array Param) (value : Code) : FunDecl

def CasesCore.extractAlt! (cases : Cases) (ctorName : Name) : Alt × Cases :=
  let found (i : Nat) := (cases.alts[i]!, { cases with alts := cases.alts.eraseIdx i })
  if let some i := cases.alts.findIdx? fun | .alt ctorName' .. => ctorName == ctorName' | _ => false then
    found i
  else if let some i := cases.alts.findIdx? fun | .default _ => true | _ => false then
    found i
  else
    unreachable!

def AltCore.mapCodeM [Monad m] (alt : Alt) (f : Code → m Code) : m Alt := do
  return alt.updateCode (← f alt.getCode)

def Code.isDecl : Code → Bool
  | .let .. | .fun .. | .jp .. => true
  | _ => false

def Code.isFun : Code → Bool
  | .fun .. => true
  | _ => false

def Code.isReturnOf : Code → FVarId → Bool
  | .return fvarId, fvarId' => fvarId == fvarId'
  | _, _ => false

partial def Code.size (c : Code) : Nat :=
  go c 0
where
  go (c : Code) (n : Nat) : Nat :=
    match c with
    | .let _ k => go k (n+1)
    | .jp decl k | .fun decl k => go k <| go decl.value n
    | .cases c => c.alts.foldl (init := n+1) fun n alt => go alt.getCode (n+1)
    | .jmp .. => n+1
    | .return .. | unreach .. => n -- `return` & `unreach` have weight zero

/-- Return true iff `c.size ≤ n` -/
partial def Code.sizeLe (c : Code) (n : Nat) : Bool :=
  match go c |>.run 0 with
  | .ok .. => true
  | .error .. => false
where
  inc : EStateM Unit Nat Unit := do
    modify (·+1)
    unless (← get) <= n do throw ()

  go (c : Code) : EStateM Unit Nat Unit := do
    match c with
    | .let _ k => inc; go k
    | .jp decl k | .fun decl k => inc; go decl.value; go k
    | .cases c => inc; c.alts.forM fun alt => go alt.getCode
    | .jmp .. => inc
    | .return .. | unreach .. => return ()

partial def Code.forM [Monad m] (c : Code) (f : Code → m Unit) : m Unit :=
  go c
where
  go (c : Code) : m Unit := do
    f c
    match c with
    | .let _ k => go k
    | .fun decl k | .jp decl k => go decl.value; go k
    | .cases c => c.alts.forM fun alt => go alt.getCode
    | .unreach .. | .return .. | .jmp .. => return ()

/--
Declaration being processed by the Lean to Lean compiler passes.
-/
structure Decl where
  /--
  The name of the declaration from the `Environment` it came from
  -/
  name  : Name
  /--
  Universe level parameter names.
  -/
  levelParams : List Name
  /--
  The type of the declaration. Note that this is an erased LCNF type
  instead of the fully dependent one that might have been the original
  type of the declaration in the `Environment`.
  -/
  type  : Expr
  /--
  Parameters.
  -/
  params : Array Param
  /--
  The body of the declaration, usually changes as it progresses
  through compiler passes.
  -/
  value : Code
  /--
  We set this flag to true during LCNF conversion. When we receive
  a block of functions to be compiled, we set this flag to `true`
  if there is an application to the function in the block containing
  it. This is an approximation, but it should be good enough because
  in the frontend, we invoke the compiler with blocks of strongly connected
  components only.
  We use this information to control inlining.
  -/
  recursive : Bool := false
  /--
  We set this flag to false during LCNF conversion if the Lean function
  associated with this function was tagged as partial or unsafe. This
  information affects how static analyzers treat function applications
  of this kind. See `DefinitionSafety`.
  `partial` and `unsafe` functions may not be terminating, but Lean
  functions terminate, and some static analyzers exploit this
  fact. So, we use the following semantics. Suppose we have a (large) natural
  number `C`. We consider a nondeterministic model for computation of Lean expressions as
  follows:
  Each call to a partial/unsafe function uses up one "recursion token".
  Prior to consuming `C` recursion tokens all partial functions must be called
  as normal. Once the model has used up `C` recursion tokens, a subsequent call to
  a partial function has the following nondeterministic options: it can either call
  the function again, or return any value of the target type (even a noncomputable one).
  Larger values of `C` yield less nondeterminism in the model, but even the intersection of
  all choices of `C` yields nondeterminism where `def loop : A := loop` returns any value of type `A`.
  The compiler fixes a choice for `C`. This is a fixed constant greater than 2^2^64,
  which is allowed to be compiler and architecture dependent, and promises that it will
  produce an execution consistent with every possible nondeterministic outcome of the `C`-model.
  In the event that different nondeterministic executions disagree, the compiler is required to
  exhaust resources or output a looping computation.
  -/
  safe : Bool := true
  /--
  We store the inline attribute at LCNF declarations to make sure we can set them for
  auxiliary declarations created during compilation.
  -/
  inlineAttr? : Option InlineAttributeKind
  deriving Inhabited, BEq

def Decl.size (decl : Decl) : Nat :=
  decl.value.size

def Decl.getArity (decl : Decl) : Nat :=
  decl.params.size

def Decl.inlineAttr (decl : Decl) : Bool :=
  decl.inlineAttr? matches some .inline

def Decl.noinlineAttr (decl : Decl) : Bool :=
  decl.inlineAttr? matches some .noinline

def Decl.inlineIfReduceAttr (decl : Decl) : Bool :=
  decl.inlineAttr? matches some .inlineIfReduce

def Decl.alwaysInlineAttr (decl : Decl) : Bool :=
  decl.inlineAttr? matches some .alwaysInline

/-- Return `true` if the given declaration has been annotated with `[inline]`, `[inline_if_reduce]`, `[macro_inline]`, or `[always_inline]` -/
def Decl.inlineable (decl : Decl) : Bool :=
  match decl.inlineAttr? with
  | some .noinline => false
  | some _ => true
  | none => false

/--
Return `some i` if `decl` is of the form
```
def f (a_0 ... a_i ...) :=
  ...
  cases a_i
  | ...
  | ...
```
That is, `f` is a sequence of declarations followed by a `cases` on the parameter `i`.
We use this function to decide whether we should inline a declaration tagged with
`[inline_if_reduce]` or not.
-/
def Decl.isCasesOnParam? (decl : Decl) : Option Nat :=
  go decl.value
where
  go (code : Code) : Option Nat :=
    match code with
    | .let _ k | .jp _ k | .fun _ k => go k
    | .cases c => decl.params.findIdx? fun param => param.fvarId == c.discr
    | _ => none

def Decl.instantiateTypeLevelParams (decl : Decl) (us : List Level) : Expr :=
  decl.type.instantiateLevelParamsNoCache decl.levelParams us

def Decl.instantiateParamsLevelParams (decl : Decl) (us : List Level) : Array Param :=
  decl.params.mapMono fun param => param.updateCore (param.type.instantiateLevelParamsNoCache decl.levelParams us)

partial def Decl.instantiateValueLevelParams (decl : Decl) (us : List Level) : Code :=
  instCode decl.value
where
  instLevel (u : Level) :=
    u.instantiateParams decl.levelParams us

  instExpr (e : Expr) :=
    e.instantiateLevelParamsNoCache decl.levelParams us

  instParams (ps : Array Param) :=
    ps.mapMono fun p => p.updateCore (instExpr p.type)

  instAlt (alt : Alt) :=
    match alt with
    | .default k => alt.updateCode (instCode k)
    | .alt _ ps k => alt.updateAlt! (instParams ps) (instCode k)

  instArg (arg : Arg) : Arg :=
    match arg with
    | .type e => arg.updateType! (instExpr e)
    | .fvar .. | .erased => arg

  instLetValue (e : LetValue) : LetValue :=
    match e with
    | .const declName vs args => e.updateConst! declName (vs.mapMono instLevel) (args.mapMono instArg)
    | .fvar fvarId args => e.updateFVar! fvarId (args.mapMono instArg)
    | .proj .. | .value .. | .erased => e

  instLetDecl (decl : LetDecl) :=
    decl.updateCore (instExpr decl.type) (instLetValue decl.value)

  instFunDecl (decl : FunDecl) :=
    decl.updateCore (instExpr decl.type) (instParams decl.params) (instCode decl.value)

  instCode (code : Code) :=
    match code with
    | .let decl k => code.updateLet! (instLetDecl decl) (instCode k)
    | .jp decl k | .fun decl k => code.updateFun! (instFunDecl decl) (instCode k)
    | .cases c => code.updateCases! (instExpr c.resultType) c.discr (c.alts.mapMono instAlt)
    | .jmp fvarId args => code.updateJmp! fvarId (args.mapMono instArg)
    | .return .. => code
    | .unreach type => code.updateUnreach! (instExpr type)

/--
Return `true` if the arrow type contains an instance implicit argument.
-/
def hasLocalInst (type : Expr) : Bool :=
  match type with
  | .forallE _ _ b bi => bi.isInstImplicit || hasLocalInst b
  | _ => false

/--
Return `true` if `decl` is supposed to be inlined/specialized.
-/
def Decl.isTemplateLike (decl : Decl) : CoreM Bool := do
  if hasLocalInst decl.type then
    return true -- `decl` applications will be specialized
  else if (← Meta.isInstance decl.name) then
    return true -- `decl` is "fuel" for code specialization
  else if decl.inlineable || hasSpecializeAttribute (← getEnv) decl.name then
    return true -- `decl` is going to be inlined or specialized
  else
    return false

private partial def collectType (e : Expr) : FVarIdSet → FVarIdSet :=
  match e with
  | .forallE _ d b _ => collectType b ∘ collectType d
  | .lam _ d b _     => collectType b ∘ collectType d
  | .app f a         => collectType f ∘ collectType a
  | .fvar fvarId     => fun s => s.insert fvarId
  | .proj .. | .letE .. | .mdata .. => unreachable!
  | _                => id

private def collectArg (arg : Arg) (s : FVarIdSet) : FVarIdSet :=
  match arg with
  | .erased => s
  | .fvar fvarId => s.insert fvarId
  | .type e => collectType e s

private def collectArgs (args : Array Arg) (s : FVarIdSet) : FVarIdSet :=
  args.foldl (init := s) fun s arg => collectArg arg s

private def collectLetValue (e : LetValue) (s : FVarIdSet) : FVarIdSet :=
  match e with
  | .fvar fvarId args => collectArgs args <| s.insert fvarId
  | .const _ _ args => collectArgs args s
  | .proj _ _ fvarId => s.insert fvarId
  | .value .. | .erased => s

private partial def collectParams (ps : Array Param) (s : FVarIdSet) : FVarIdSet :=
  ps.foldl (init := s) fun s p => collectType p.type s

mutual
partial def FunDeclCore.collectUsed (decl : FunDecl) (s : FVarIdSet := {}) : FVarIdSet :=
  decl.value.collectUsed <| collectParams decl.params <| collectType decl.type s

partial def Code.collectUsed (code : Code) (s : FVarIdSet := {}) : FVarIdSet :=
  match code with
  | .let decl k => k.collectUsed <| collectLetValue decl.value <| collectType decl.type s
  | .jp decl k | .fun decl k => k.collectUsed <| decl.collectUsed s
  | .cases c =>
    let s := s.insert c.discr
    let s := collectType c.resultType s
    c.alts.foldl (init := s) fun s alt =>
      match alt with
      | .default k => k.collectUsed s
      | .alt _ ps k => k.collectUsed <| collectParams ps s
  | .return fvarId => s.insert fvarId
  | .unreach type => collectType type s
  | .jmp fvarId args => collectArgs args <| s.insert fvarId
end

abbrev collectUsedAtExpr (s : FVarIdSet) (e : Expr) : FVarIdSet :=
  collectType e s

/--
Traverse the given block of potentially mutually recursive functions
and mark a declaration `f` as recursive if there is an application
`f ...` in the block.
This is an overapproximation, and relies on the fact that our frontend
computes strongly connected components.
See comment at `recursive` field.
-/
partial def markRecDecls (decls : Array Decl) : Array Decl :=
  let (_, isRec) := go |>.run {}
  decls.map fun decl =>
    if isRec.contains decl.name then
      { decl with recursive := true }
    else
      decl
where
  visit (code : Code) : StateM NameSet Unit := do
    match code with
    | .jp decl k | .fun decl k => visit decl.value; visit k
    | .cases c => c.alts.forM fun alt => visit alt.getCode
    | .unreach .. | .jmp .. | .return .. => return ()
    | .let decl k =>
      if let .const declName _ _ := decl.value then
        if decls.any (·.name == declName) then
          modify fun s => s.insert declName
      visit k

  go : StateM NameSet Unit :=
    decls.forM fun decl => visit decl.value

def instantiateRangeArgs (e : Expr) (beginIdx endIdx : Nat) (args : Array Arg) : Expr :=
  if !e.hasLooseBVars then
    e
  else
    e.instantiateRange beginIdx endIdx (args.map (·.toExpr))

def instantiateRevRangeArgs (e : Expr) (beginIdx endIdx : Nat) (args : Array Arg) : Expr :=
  if !e.hasLooseBVars then
    e
  else
    e.instantiateRevRange beginIdx endIdx (args.map (·.toExpr))

end Lean.Compiler.LCNF
