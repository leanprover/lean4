/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Instances
public import Lean.Compiler.ExternAttr
public import Lean.Compiler.Specialize
public import Lean.Compiler.LCNF.Types
import Init.Omega

public section

namespace Lean.Compiler.LCNF

/-!
# Lean Compiler Normal Form (LCNF)

It is based on the [A-normal form](https://en.wikipedia.org/wiki/A-normal_form),
and the approach described in the paper
[Compiling  without continuations](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/compiling-without-continuations.pdf).

-/

/--
This type is used to index the fundamental LCNF IR data structures. Depending on its value different
constructors are available for the different semantic phases of LCNF.

Notably in order to save memory we never index the IR types over `Purity`. Instead the type is
parametrized by the phase and the individual constructors might carry a proof (that will be erased)
that they are only allowed in a certain phase.
-/
inductive Purity where
  /--
  The code we are acting on is still pure, things like reordering up to value dependencies are
  acceptable.
  -/
  | pure
  /--
  The code we are acting on is to be considered generally impure, doing reorderings is potentially
  no longer legal.
  -/
  | impure
  deriving Inhabited, DecidableEq, Hashable

instance : ToString Purity where
  toString
    | .pure => "pure"
    | .impure => "impure"

@[inline]
def Purity.withAssertPurity [Inhabited α] (is : Purity) (should : Purity)
    (k : (is = should) → α) : α :=
  if h : is = should then
    k h
  else
    panic! s!"Purity should be {should} but is {is}, this is a bug"

scoped macro "purity_tac" : tactic => `(tactic| first | with_reducible rfl | assumption)

structure Param (pu : Purity) where
  fvarId     : FVarId
  binderName : Name
  type       : Expr
  borrow     : Bool
  deriving Inhabited, BEq

def Param.toExpr (p : Param pu) : Expr :=
  .fvar p.fvarId

inductive LitValue where
  | nat (val : Nat)
  | str (val : String)
  | uint8 (val : UInt8)
  | uint16 (val : UInt16)
  | uint32 (val : UInt32)
  | uint64 (val : UInt64)
  -- USize has a maximum size of 64 bits
  | usize (val : UInt64)
  -- TODO: add constructors for `Int`, `Float`, ...
  deriving Inhabited, BEq, Hashable

def LitValue.toExpr : LitValue → Expr
  | .nat v => .lit (.natVal v)
  | .str v => .lit (.strVal v)
  | .uint8 v => .app (.const ``UInt8.ofNat []) (.lit (.natVal (UInt8.toNat v)))
  | .uint16 v => .app (.const ``UInt16.ofNat []) (.lit (.natVal (UInt16.toNat v)))
  | .uint32 v => .app (.const ``UInt32.ofNat []) (.lit (.natVal (UInt32.toNat v)))
  | .uint64 v => .app (.const ``UInt64.ofNat []) (.lit (.natVal (UInt64.toNat v)))
  | .usize v => .app (.const ``USize.ofNat []) (.lit (.natVal (UInt64.toNat v)))

def LitValue.impureTypeScalarNumLit (e : Expr) (n : Nat) : LitValue :=
  match e with
  | ImpureType.uint8 => .uint8 n.toUInt8
  | ImpureType.uint16 => .uint16 n.toUInt16
  | ImpureType.uint32 => .uint32 n.toUInt32
  | ImpureType.uint64 => .uint64 n.toUInt64
  | ImpureType.usize => .usize n.toUInt64
  | _ => panic! s!"Provided invalid type to impureTypeScalarNumLit: {e}"

inductive Arg (pu : Purity) where
  | erased
  | fvar (fvarId : FVarId)
  | type (expr : Expr) (h : pu = .pure := by purity_tac)
  deriving Inhabited, BEq, Hashable

def Param.toArg (p : Param pu) : Arg pu :=
  .fvar p.fvarId

def Arg.toExpr (arg : Arg pu) : Expr :=
  match arg with
  | .erased => erasedExpr
  | .fvar fvarId => .fvar fvarId
  | .type e _ => e

private unsafe def Arg.updateTypeImp (arg : Arg pu) (type' : Expr) : Arg pu :=
  match arg with
  | .type ty _ => if ptrEq ty type' then arg else .type type'
  | _ => unreachable!

@[implemented_by Arg.updateTypeImp] opaque Arg.updateType! (arg : Arg pu) (type : Expr) : Arg pu

private unsafe def Arg.updateFVarImp (arg : Arg pu) (fvarId' : FVarId) : Arg pu :=
  match arg with
  | .fvar fvarId => if fvarId' == fvarId then arg else .fvar fvarId'
  | _ => unreachable!

@[implemented_by Arg.updateFVarImp] opaque Arg.updateFVar! (arg : Arg pu) (fvarId' : FVarId) : Arg pu

/-- Constructor information.

   - `name` is the Name of the Constructor in Lean.
   - `cidx` is the Constructor index (aka tag).
   - `size` is the number of arguments of type `object/tobject`.
   - `usize` is the number of arguments of type `usize`.
   - `ssize` is the number of bytes used to store scalar values.

Recall that a Constructor object contains a header, then a sequence of
pointers to other Lean objects, a sequence of `USize` (i.e., `size_t`)
scalar values, and a sequence of other scalar values. -/
structure CtorInfo where
  name : Name
  cidx : Nat
  size : Nat
  usize : Nat
  ssize : Nat
  deriving Inhabited, BEq, Repr, Hashable

def CtorInfo.isRef (info : CtorInfo) : Bool :=
  info.size > 0 || info.usize > 0 || info.ssize > 0

def CtorInfo.isScalar (info : CtorInfo) : Bool :=
  !info.isRef

def CtorInfo.type (info : CtorInfo) : Expr :=
  if info.isRef then ImpureType.object else ImpureType.tagged

inductive LetValue (pu : Purity) where
  /--
  A literal value.
  -/
  | lit (value : LitValue)
  /--
  An erased value that is irrelevant for computation.
  -/
  | erased
  /--
  A projection from a pure LCNF value.
  -/
  | proj (typeName : Name) (idx : Nat) (struct : FVarId) (h : pu = .pure := by purity_tac)
  /--
  A pure application of a constant.
  -/
  | const (declName : Name) (us : List Level) (args : Array (Arg pu)) (h : pu = .pure := by purity_tac)
  /--
  An application of a free variable
  -/
  | fvar (fvarId : FVarId) (args : Array (Arg pu))
  /--
  Allocating a constructor.
  -/
  | ctor (i : CtorInfo) (args : Array (Arg pu)) (h : pu = .impure := by purity_tac)
  /--
  Projecting objects out of a value.
  -/
  | oproj (i : Nat) (var : FVarId) (h : pu = .impure := by purity_tac)
  /--
  Projecting USize scalars out of a value.
  -/
  | uproj (i : Nat) (var : FVarId) (h : pu = .impure := by purity_tac)
  /--
  Projecting non-USize scalars out of a value
  -/
  | sproj (n : Nat) (offset : Nat) (var : FVarId) (h : pu = .impure := by purity_tac)
  /--
  Full, impure, application of a function.
  -/
  | fap (fn : Name) (args : Array (Arg pu)) (h : pu = .impure := by purity_tac)
  /--
  Partial application of a function.
  -/
  | pap (fn : Name) (args : Array (Arg pu)) (h : pu = .impure := by purity_tac)
  /--
  The reset instruction from Counting Immutable Beans. `n` is the amount of object fields stored in
  the constructor in `var`.
  -/
  | reset (n : Nat) (var : FVarId) (h : pu = .impure := by purity_tac)
  /-- `reuse x in ctor_i ys` instruction in the paper. `updateHeader` is set if the tag in the new
      ctor differs from the one in the old ctor and thus needs to be updated. -/
  | reuse (var : FVarId) (i : CtorInfo) (updateHeader : Bool) (args : Array (Arg pu)) (h : pu = .impure := by purity_tac)
  /--
  Given a scalar type `ty` and a value `fvarId : ty`, this operation returns a value of type
  `tobject`. For small scalar values the result is a tagged pointer, and no memory allocation is
  performed.
  -/
  | box (ty : Expr) (fvarId : FVarId) (h : pu = .impure := by purity_tac)
  /-- Given `fvarId : [t]object`, obtain the underlying scalar value. -/
  | unbox (fvarId : FVarId) (h : pu = .impure := by purity_tac)
  deriving Inhabited, BEq, Hashable

def Arg.toLetValue (arg : Arg pu) : LetValue pu :=
  match arg with
  | .fvar fvarId => .fvar fvarId #[]
  | .erased | .type .. => .erased

private unsafe def LetValue.updateProjImp (e : LetValue pu) (fvarId' : FVarId) : LetValue pu :=
  match e with
  | .proj s i fvarId _ => if fvarId == fvarId' then e else .proj s i fvarId'
  | .sproj i offset fvarId _ => if fvarId == fvarId' then e else .sproj i offset fvarId'
  | .uproj i fvarId _ => if fvarId == fvarId' then e else .uproj i fvarId'
  | .oproj i fvarId _ => if fvarId == fvarId' then e else .oproj i fvarId'
  | _ => unreachable!

@[implemented_by LetValue.updateProjImp] opaque LetValue.updateProj! (e : LetValue pu) (fvarId' : FVarId) : LetValue pu

private unsafe def LetValue.updateConstImp (e : LetValue pu) (declName' : Name) (us' : List Level) (args' : Array (Arg pu)) : LetValue pu :=
  match e with
  | .const declName us args _ => if declName == declName' && ptrEq us us' && ptrEq args args' then e else .const declName' us' args'
  | _ => unreachable!

@[implemented_by LetValue.updateConstImp] opaque LetValue.updateConst! (e : LetValue pu) (declName' : Name) (us' : List Level) (args' : Array (Arg pu)) : LetValue pu

private unsafe def LetValue.updateFVarImp (e : LetValue pu) (fvarId' : FVarId) (args' : Array (Arg pu)) : LetValue pu :=
  match e with
  | .fvar fvarId args => if fvarId == fvarId' && ptrEq args args' then e else .fvar fvarId' args'
  | _ => unreachable!

@[implemented_by LetValue.updateFVarImp] opaque LetValue.updateFVar! (e : LetValue pu) (fvarId' : FVarId) (args' : Array (Arg pu)) : LetValue pu

private unsafe def LetValue.updateResetImp (e : LetValue pu) (n' : Nat) (fvarId' : FVarId) : LetValue pu :=
  match e with
  | .reset n fvarId _ => if n == n' && fvarId == fvarId' then e else .reset n' fvarId'
  | _ => unreachable!

@[implemented_by LetValue.updateResetImp] opaque LetValue.updateReset! (e : LetValue pu) (n' : Nat) (fvarId' : FVarId) : LetValue pu

private unsafe def LetValue.updateReuseImp (e : LetValue pu) (var' : FVarId) (i' : CtorInfo)
    (updateHeader' : Bool) (args' : Array (Arg pu)) : LetValue pu :=
  match e with
  | .reuse var i updateHeader args _ =>
    if var == var' && ptrEq i i' && updateHeader == updateHeader' && ptrEq args args' then
      e
    else
      .reuse var' i' updateHeader' args'
  | _ => unreachable!

@[implemented_by LetValue.updateReuseImp] opaque LetValue.updateReuse! (e : LetValue pu)
    (var' : FVarId) (i' : CtorInfo) (updateHeader' : Bool) (args' : Array (Arg pu)) : LetValue pu

private unsafe def LetValue.updateFapImp (e : LetValue pu) (declName' : Name) (args' : Array (Arg pu)) : LetValue pu :=
  match e with
  | .fap declName args _ => if declName == declName' && ptrEq args args' then e else .fap declName' args'
  | _ => unreachable!

@[implemented_by LetValue.updateFapImp] opaque LetValue.updateFap! (e : LetValue pu) (declName' : Name) (args' : Array (Arg pu)) : LetValue pu

private unsafe def LetValue.updatePapImp (e : LetValue pu) (declName' : Name) (args' : Array (Arg pu)) : LetValue pu :=
  match e with
  | .pap declName args _ => if declName == declName' && ptrEq args args' then e else .pap declName' args'
  | _ => unreachable!

@[implemented_by LetValue.updatePapImp] opaque LetValue.updatePap! (e : LetValue pu) (declName' : Name) (args' : Array (Arg pu)) : LetValue pu

private unsafe def LetValue.updateBoxImp (e : LetValue pu) (ty' : Expr) (fvarId' : FVarId) : LetValue pu :=
  match e with
  | .box ty fvarId _ => if ptrEq ty ty' && fvarId == fvarId' then e else .box ty' fvarId'
  | _ => unreachable!

@[implemented_by LetValue.updateBoxImp] opaque LetValue.updateBox! (e : LetValue pu) (ty' : Expr) (fvarId' : FVarId) : LetValue pu

private unsafe def LetValue.updateUnboxImp (e : LetValue pu) (fvarId' : FVarId) : LetValue pu :=
  match e with
  | .unbox fvarId _ => if fvarId == fvarId' then e else .unbox fvarId'
  | _ => unreachable!

@[implemented_by LetValue.updateUnboxImp] opaque LetValue.updateUnbox! (e : LetValue pu) (fvarId' : FVarId) : LetValue pu



private unsafe def LetValue.updateArgsImp (e : LetValue pu) (args' : Array (Arg pu)) : LetValue pu :=
  match e with
  | .const declName us args h => if ptrEq args args' then e else .const declName us args'
  | .fvar fvarId args => if ptrEq args args' then e else .fvar fvarId args'
  | .pap declName args _  => if ptrEq args args' then e else .pap declName args'
  | .fap declName args _  => if ptrEq args args' then e else .fap declName args'
  | .ctor info args _  => if ptrEq args args' then e else .ctor info args'
  | .reuse var info updateHeader args _ =>
    if ptrEq args args' then e else .reuse var info updateHeader args'
  | _ => unreachable!

@[implemented_by LetValue.updateArgsImp] opaque LetValue.updateArgs! (e : LetValue pu) (args' : Array (Arg pu)) : LetValue pu

def LetValue.toExpr (e : LetValue pu) : Expr :=
  match e with
  | .lit v => v.toExpr
  | .erased => erasedExpr
  | .proj n i s _ => .proj n i (.fvar s)
  | .const n us as _ => mkAppN (.const n us) (as.map Arg.toExpr)
  | .fvar fvarId as => mkAppN (.fvar fvarId) (as.map Arg.toExpr)
  | .ctor i as _ => mkAppN (.const i.name []) (as.map Arg.toExpr)
  | .fap fn as _ | .pap fn as _ => mkAppN (.const fn []) (as.map Arg.toExpr)
  | .oproj i var _ => mkApp2 (.const `oproj []) (ToExpr.toExpr i) (.fvar var)
  | .uproj i var _ => mkApp2 (.const `uproj []) (ToExpr.toExpr i) (.fvar var)
  | .sproj i offset var _ => mkApp3 (.const `sproj []) (ToExpr.toExpr i) (ToExpr.toExpr offset) (.fvar var)
  | .reset n var _ => mkApp2 (.const `reset []) (ToExpr.toExpr n) (.fvar var)
  | .reuse var i updateHeader args _ =>
    mkAppN (.const `reuse []) <|
      #[.fvar var, .const i.name [], ToExpr.toExpr updateHeader] ++ (args.map Arg.toExpr)
  | .box ty var _ => mkApp2 (.const `box []) ty (.fvar var)
  | .unbox var _ => mkApp (.const `unbox []) (.fvar var)

structure LetDecl (pu : Purity) where
  fvarId : FVarId
  binderName : Name
  type : Expr
  value : LetValue pu
  deriving Inhabited, BEq

mutual

inductive Alt (pu : Purity) where
  | alt (ctorName : Name) (params : Array (Param pu)) (code : Code pu) (h : pu = .pure := by purity_tac)
  | ctorAlt (info : CtorInfo) (code : Code pu) (h : pu = .impure := by purity_tac)
  | default (code : Code pu)

inductive FunDecl (pu : Purity) where
  | mk (fvarId : FVarId) (binderName : Name) (params : Array (Param pu)) (type : Expr) (value : Code pu)

inductive Cases (pu : Purity) where
  | mk (typeName : Name) (resultType : Expr) (discr : FVarId) (alts : Array (Alt pu))
  deriving Inhabited

inductive Code (pu : Purity) where
  | let (decl : LetDecl pu) (k : Code pu)
  | fun (decl : FunDecl pu) (k : Code pu) (h : pu = .pure := by purity_tac)
  | jp (decl : FunDecl pu) (k : Code pu)
  | jmp (fvarId : FVarId) (args : Array (Arg pu))
  | cases (cases : Cases pu)
  | return (fvarId : FVarId)
  | unreach (type : Expr)
  | uset (var : FVarId) (i : Nat) (y : FVarId) (k : Code pu) (h : pu = .impure := by purity_tac)
  | sset (var : FVarId) (i : Nat) (offset : Nat) (y : FVarId) (ty : Expr) (k : Code pu) (h : pu = .impure := by purity_tac)
  | inc (fvarId : FVarId) (n : Nat) (check : Bool) (persistent : Bool) (k : Code pu) (h : pu = .impure := by purity_tac)
  | dec (fvarId : FVarId) (n : Nat) (check : Bool) (persistent : Bool) (k : Code pu) (h : pu = .impure := by purity_tac)
  deriving Inhabited

end

@[inline]
def FunDecl.fvarId : FunDecl pu → FVarId
  | .mk (fvarId := fvarId) .. => fvarId

@[inline]
def FunDecl.binderName : FunDecl pu → Name
  | .mk (binderName := binderName) .. => binderName

@[inline]
def FunDecl.params : FunDecl pu → Array (Param pu)
  | .mk (params := params) .. => params

@[inline]
def FunDecl.type : FunDecl pu → Expr
  | .mk (type := type) .. => type

@[inline]
def FunDecl.value : FunDecl pu → Code pu
  | .mk (value := value) .. => value

@[inline]
def FunDecl.updateBinderName : FunDecl pu → Name → FunDecl pu
  | .mk fvarId _ params type value, new =>
    .mk fvarId new params type value

@[inline]
def FunDecl.toParam (decl : FunDecl pu) (borrow : Bool) : Param pu :=
  match decl with
  | .mk fvarId binderName _ type .. => ⟨fvarId, binderName, type, borrow⟩

@[inline]
def Cases.typeName : Cases pu → Name
  | .mk (typeName := typeName) .. => typeName

@[inline]
def Cases.resultType : Cases pu → Expr
  | .mk (resultType := resultType) .. => resultType

@[inline]
def Cases.discr : Cases pu → FVarId
  | .mk (discr := discr) .. => discr

@[inline]
def Cases.alts : Cases pu → Array (Alt pu)
  | .mk (alts := alts) .. => alts

@[inline]
def Cases.updateAlts : Cases pu → Array (Alt pu) → Cases pu
  | .mk typeName resultType discr _, new =>
    .mk typeName resultType discr new

deriving instance Inhabited for Alt
deriving instance Inhabited for FunDecl

def FunDecl.getArity (decl : FunDecl pu) : Nat :=
  decl.params.size

/--
Return the constructor names that have an explicit (non-default) alternative.
-/
def Cases.getCtorNames (c : Cases pu) : NameSet :=
  c.alts.foldl (init := {}) fun ctorNames alt =>
    match alt with
    | .default _ => ctorNames
    | .alt ctorName .. => ctorNames.insert ctorName
    | .ctorAlt info .. => ctorNames.insert info.name

inductive CodeDecl (pu : Purity) where
  | let (decl : LetDecl pu)
  | fun (decl : FunDecl pu) (h : pu = .pure := by purity_tac)
  | jp (decl : FunDecl pu)
  | uset (var : FVarId) (i : Nat) (y : FVarId) (h : pu = .impure := by purity_tac)
  | sset (var : FVarId) (i : Nat) (offset : Nat) (y : FVarId)  (ty : Expr) (h : pu = .impure := by purity_tac)
  | inc (fvarId : FVarId) (n : Nat) (check : Bool) (persistent : Bool) (h : pu = .impure := by purity_tac)
  | dec (fvarId : FVarId) (n : Nat) (check : Bool) (persistent : Bool) (h : pu = .impure := by purity_tac)
  deriving Inhabited

def CodeDecl.fvarId : CodeDecl pu → FVarId
  | .let decl | .fun decl _ | .jp decl => decl.fvarId
  | .uset fvarId .. | .sset fvarId .. | .inc fvarId .. | .dec fvarId .. => fvarId

def Code.toCodeDecl! : Code pu → CodeDecl pu
| .let decl _ => .let decl
| .fun decl _ _ => .fun decl
| .jp decl _ => .jp decl
| .uset var i y _ _ => .uset var i y
| .sset var i offset ty y _ _ => .sset var i offset ty y
| .inc fvarId n check persistent _ _ => .inc fvarId n check persistent
| .dec fvarId n check persistent _ _ => .dec fvarId n check persistent
| _ => unreachable!

def attachCodeDecls (decls : Array (CodeDecl pu)) (code : Code pu) : Code pu :=
  go decls.size code
where
  go (i : Nat) (code : Code pu) : Code pu :=
    if i > 0 then
      match decls[i-1]! with
      | .let decl => go (i-1) (.let decl code)
      | .fun decl _ => go (i-1) (.fun decl code)
      | .jp decl => go (i-1) (.jp decl code)
      | .uset var idx y _ => go (i-1) (.uset var idx y code)
      | .sset var idx offset y ty _ => go (i-1) (.sset var idx offset y ty code)
      | .inc fvarId n check persistent _ => go (i-1) (.inc fvarId n check persistent code)
      | .dec fvarId n check persistent _ => go (i-1) (.dec fvarId n check persistent code)
    else
      code

mutual
  private unsafe def eqImp (c₁ c₂ : Code pu) : Bool :=
    if ptrEq c₁ c₂ then
      true
    else match c₁, c₂ with
      | .let d₁ k₁, .let d₂ k₂ => d₁ == d₂ && eqImp k₁ k₂
      | .fun d₁ k₁ _, .fun d₂ k₂ _
      | .jp d₁ k₁, .jp d₂ k₂ => eqFunDecl d₁ d₂ && eqImp k₁ k₂
      | .cases c₁, .cases c₂ => eqCases c₁ c₂
      | .jmp j₁ as₁, .jmp j₂ as₂ => j₁ == j₂ && as₁ == as₂
      | .return r₁, .return r₂ => r₁ == r₂
      | .unreach t₁, .unreach t₂ => t₁ == t₂
      | .uset v₁ i₁ y₁ k₁ _, .uset v₂ i₂ y₂ k₂ _ =>
        v₁ == v₂ && i₁ == i₂ && y₁ == y₂ && eqImp k₁ k₂
      | .sset v₁ i₁ o₁ y₁ ty₁ k₁ _, .sset v₂ i₂ o₂ y₂ ty₂ k₂ _ =>
        v₁ == v₂ && i₁ == i₂ && o₁ == o₂ && y₁ == y₂ && ty₁ == ty₂ && eqImp k₁ k₂
      | .inc v₁ n₁ c₁ p₁ k₁ _, .inc v₂ n₂ c₂ p₂ k₂ _ =>
        v₁ == v₂ && n₁ == n₂ && c₁ == c₂ && p₁ == p₂ && eqImp k₁ k₂
      | .dec v₁ n₁ c₁ p₁ k₁ _, .dec v₂ n₂ c₂ p₂ k₂ _ =>
        v₁ == v₂ && n₁ == n₂ && c₁ == c₂ && p₁ == p₂ && eqImp k₁ k₂
      | _, _ => false

  private unsafe def eqFunDecl (d₁ d₂ : FunDecl pu) : Bool :=
    if ptrEq d₁ d₂ then
      true
    else
      d₁.fvarId == d₂.fvarId && d₁.binderName == d₂.binderName &&
      d₁.params == d₂.params && d₁.type == d₂.type &&
      eqImp d₁.value d₂.value

  private unsafe def eqCases (c₁ c₂ : Cases pu) : Bool :=
    c₁.resultType == c₂.resultType && c₁.discr == c₂.discr &&
    c₁.typeName == c₂.typeName && c₁.alts.isEqv c₂.alts eqAlt

  private unsafe def eqAlt (a₁ a₂ : Alt pu) : Bool :=
    match a₁, a₂ with
    | .default k₁, .default k₂ => eqImp k₁ k₂
    | .alt c₁ ps₁ k₁ _, .alt c₂ ps₂ k₂ _ => c₁ == c₂ && ps₁ == ps₂ && eqImp k₁ k₂
    | .ctorAlt i₁ k₁ _, .ctorAlt i₂ k₂ _ => i₁ == i₂ && eqImp k₁ k₂
    | _, _ => false
end

@[implemented_by eqImp] protected opaque Code.beq : Code pu → Code pu → Bool

instance : BEq (Code pu) where
  beq := Code.beq

@[implemented_by eqFunDecl] protected opaque FunDecl.beq : FunDecl pu → FunDecl pu → Bool

instance : BEq (FunDecl pu) where
  beq := FunDecl.beq

def Alt.getCode : Alt pu → Code pu
  | .default k => k
  | .alt _ _ k _ => k
  | .ctorAlt _ k _ => k

def Alt.getParams : Alt .pure → Array (Param .pure)
  | .default _ => #[]
  | .alt _ ps _ _ => ps

def Alt.forCodeM [Monad m] (alt : Alt pu) (f : Code pu → m Unit) : m Unit := do
  match alt with
  | .default k => f k
  | .alt _ _ k _ => f k
  | .ctorAlt _ k _ => f k

private unsafe def updateAltCodeImp (alt : Alt pu) (k' : Code pu) : Alt pu :=
  match alt with
  | .default k => if ptrEq k k' then alt else .default k'
  | .alt ctorName ps k _ => if ptrEq k k' then alt else .alt ctorName ps k'
  | .ctorAlt info k _ => if ptrEq k k' then alt else .ctorAlt info k'

@[implemented_by updateAltCodeImp] opaque Alt.updateCode (alt : Alt pu) (c : Code pu) : Alt pu

private unsafe def updateAltImp (alt : Alt pu) (ps' : Array (Param pu)) (k' : Code pu) : Alt pu :=
  match alt with
  | .alt ctorName ps k _ => if ptrEq k k' && ptrEq ps ps' then alt else .alt ctorName ps' k'
  | _ => unreachable!

@[implemented_by updateAltImp] opaque Alt.updateAlt! (alt : Alt pu) (ps' : Array (Param pu)) (k' : Code pu) : Alt pu

@[inline] private unsafe def updateAltsImp (c : Code pu) (alts : Array (Alt pu)) : Code pu :=
  match c with
  | .cases cs => if ptrEq cs.alts alts then c else .cases <| cs.updateAlts alts
  | _ => unreachable!

@[implemented_by updateAltsImp] opaque Code.updateAlts! (c : Code pu) (alts : Array (Alt pu)) : Code pu

@[inline] private unsafe def updateCasesImp (c : Code pu) (resultType : Expr) (discr : FVarId) (alts : Array (Alt pu)) : Code pu :=
  match c with
  | .cases cs =>
    if ptrEq cs.alts alts && ptrEq cs.resultType resultType && cs.discr == discr then
      c
    else
      .cases <| ⟨cs.typeName, resultType, discr, alts⟩
  | _ => unreachable!

@[implemented_by updateCasesImp] opaque Code.updateCases! (c : Code pu) (resultType : Expr) (discr : FVarId) (alts : Array (Alt pu)) : Code pu

@[inline] private unsafe def updateLetImp (c : Code pu) (decl' : LetDecl pu) (k' : Code pu) : Code pu :=
  match c with
  | .let decl k => if ptrEq k k' && ptrEq decl decl' then c else .let decl' k'
  | _ => unreachable!

@[implemented_by updateLetImp] opaque Code.updateLet! (c : Code pu) (decl' : LetDecl pu) (k' : Code pu) : Code pu

@[inline] private unsafe def updateContImp (c : Code pu) (k' : Code pu) : Code pu :=
  match c with
  | .let decl k => if ptrEq k k' then c else .let decl k'
  | .fun decl k _ => if ptrEq k k' then c else .fun decl k'
  | .jp decl k => if ptrEq k k' then c else .jp decl k'
  | .sset fvarId i offset y ty k _ => if ptrEq k k' then c else .sset fvarId i offset y ty k'
  | .uset fvarId offset y k _ => if ptrEq k k' then c else .uset fvarId offset y k'
  | .inc fvarId n check persistent k _ => if ptrEq k k' then c else .inc fvarId n check persistent k'
  | .dec fvarId n check persistent k _ => if ptrEq k k' then c else .dec fvarId n check persistent k'
  | _ => unreachable!

@[implemented_by updateContImp] opaque Code.updateCont! (c : Code pu) (k' : Code pu) : Code pu

@[inline] private unsafe def updateFunImp (c : Code pu) (decl' : FunDecl pu) (k' : Code pu) : Code pu :=
  match c with
  | .fun decl k _ => if ptrEq k k' && ptrEq decl decl' then c else .fun decl' k'
  | .jp decl k => if ptrEq k k' && ptrEq decl decl' then c else .jp decl' k'
  | _ => unreachable!

@[implemented_by updateFunImp] opaque Code.updateFun! (c : Code pu) (decl' : FunDecl pu) (k' : Code pu) : Code pu

@[inline] private unsafe def updateReturnImp (c : Code pu) (fvarId' : FVarId) : Code pu :=
  match c with
  | .return fvarId => if fvarId == fvarId' then c else .return fvarId'
  | _ => unreachable!

@[implemented_by updateReturnImp] opaque Code.updateReturn! (c : Code pu) (fvarId' : FVarId) : Code pu

@[inline] private unsafe def updateJmpImp (c : Code pu) (fvarId' : FVarId) (args' : Array (Arg pu)) : Code pu :=
  match c with
  | .jmp fvarId args => if fvarId == fvarId' && ptrEq args args' then c else .jmp fvarId' args'
  | _ => unreachable!

@[implemented_by updateJmpImp] opaque Code.updateJmp! (c : Code pu) (fvarId' : FVarId) (args' : Array (Arg pu)) : Code pu

@[inline] private unsafe def updateUnreachImp (c : Code pu) (type' : Expr) : Code pu :=
  match c with
  | .unreach type => if ptrEq type type' then c else .unreach type'
  | _ => unreachable!

@[implemented_by updateUnreachImp] opaque Code.updateUnreach! (c : Code pu) (type' : Expr) : Code pu

@[inline] private unsafe def updateSsetImp (c : Code pu) (fvarId' : FVarId) (i' : Nat)
    (offset' : Nat) (y' : FVarId) (ty' : Expr) (k' : Code pu) : Code pu :=
  match c with
  | .sset fvarId i offset y ty k _ =>
    if ptrEq fvarId fvarId' && i == i' && offset == offset' && ptrEq y y' && ptrEq ty ty' && ptrEq k k' then
      c
    else
      .sset fvarId' i' offset' y' ty' k'
  | _ => unreachable!

@[implemented_by updateSsetImp] opaque Code.updateSset! (c : Code pu) (fvarId' : FVarId) (i' : Nat)
    (offset' : Nat) (y' : FVarId) (ty' : Expr) (k' : Code pu) : Code pu

@[inline] private unsafe def updateUsetImp (c : Code pu) (fvarId' : FVarId)
    (i' : Nat) (y' : FVarId) (k' : Code pu) : Code pu :=
  match c with
  | .uset fvarId i y k _ =>
    if ptrEq fvarId fvarId' && i == i' && ptrEq y y' && ptrEq k k' then
      c
    else
      .uset fvarId' i' y' k'
  | _ => unreachable!

@[implemented_by updateUsetImp] opaque Code.updateUset! (c : Code pu) (fvarId' : FVarId)
    (i' : Nat) (y' : FVarId) (k' : Code pu) : Code pu

@[inline] private unsafe def updateIncImp (c : Code pu) (fvarId' : FVarId) (n' : Nat)
    (check' : Bool) (persistent' : Bool) (k' : Code pu) : Code pu :=
  match c with
  | .inc fvarId n check persistent k _ =>
    if ptrEq fvarId fvarId'
        && n == n'
        && check == check'
        && persistent == persistent'
        && ptrEq k k' then
      c
    else
      .inc fvarId' n' check' persistent' k'
  | _ => unreachable!

@[implemented_by updateIncImp] opaque Code.updateInc! (c : Code pu) (fvarId' : FVarId) (n' : Nat)
    (check' : Bool) (persistent' : Bool) (k' : Code pu) : Code pu

@[inline] private unsafe def updateDecImp (c : Code pu) (fvarId' : FVarId) (n' : Nat)
    (check' : Bool) (persistent' : Bool) (k' : Code pu) : Code pu :=
  match c with
  | .dec fvarId n check persistent k _ =>
    if ptrEq fvarId fvarId'
        && n == n'
        && check == check'
        && persistent == persistent'
        && ptrEq k k' then
      c
    else
      .dec fvarId' n' check' persistent' k'
  | _ => unreachable!

@[implemented_by updateDecImp] opaque Code.updateDec! (c : Code pu) (fvarId' : FVarId) (n' : Nat)
    (check' : Bool) (persistent' : Bool) (k' : Code pu) : Code pu

private unsafe def updateParamCoreImp (p : Param pu) (type : Expr) : Param pu :=
  if ptrEq type p.type then
    p
  else
    { p with type }

/--
Low-level update `Param` function. It does not update the local context.
Consider using `Param.update : Param → Expr → CompilerM Param` if you want the local context
to be updated.
-/
@[implemented_by updateParamCoreImp] opaque Param.updateCore (p : Param pu) (type : Expr) : Param pu

private unsafe def updateLetDeclCoreImp (decl : LetDecl pu) (type : Expr) (value : LetValue pu) : LetDecl pu :=
  if ptrEq type decl.type && ptrEq value decl.value then
    decl
  else
    { decl with type, value }

/--
Low-level update `LetDecl` function. It does not update the local context.
Consider using `LetDecl.update : LetDecl → Expr → Expr → CompilerM LetDecl` if you want the local context
to be updated.
-/
@[implemented_by updateLetDeclCoreImp] opaque LetDecl.updateCore (decl : LetDecl pu) (type : Expr) (value : LetValue pu) : LetDecl pu

private unsafe def updateFunDeclCoreImp (decl: FunDecl pu) (type : Expr) (params : Array (Param pu)) (value : Code pu) : FunDecl pu :=
  if ptrEq type decl.type && ptrEq params decl.params && ptrEq value decl.value then
    decl
  else
    ⟨decl.fvarId, decl.binderName, params, type, value⟩

/--
Low-level update `FunDecl` function. It does not update the local context.
Consider using `FunDecl.update : LetDecl → Expr → Array Param → Code → CompilerM FunDecl` if you want the local context
to be updated.
-/
@[implemented_by updateFunDeclCoreImp] opaque FunDecl.updateCore (decl : FunDecl pu) (type : Expr) (params : Array (Param pu)) (value : Code pu) : FunDecl pu

def Cases.extractAlt! (cases : Cases pu) (ctorName : Name) : Alt pu × Cases pu :=
  let found i := (cases.alts[i]!, cases.updateAlts (cases.alts.eraseIdx! i))
  if let some i := cases.alts.findFinIdx? fun | .alt ctorName' .. => ctorName == ctorName' | _ => false then
    found i
  else if let some i := cases.alts.findFinIdx? fun | .default _ => true | _ => false then
    found i
  else
    unreachable!

def Alt.mapCodeM [Monad m] (alt : Alt pu) (f : Code pu → m (Code pu)) : m (Alt pu) := do
  return alt.updateCode (← f alt.getCode)

def Code.isDecl : Code pu → Bool
  | .let .. | .fun .. | .jp .. => true
  | _ => false

def Code.isFun : Code pu → Bool
  | .fun .. => true
  | _ => false

def Code.isReturnOf : Code pu → FVarId → Bool
  | .return fvarId, fvarId' => fvarId == fvarId'
  | _, _ => false

partial def Code.size (c : Code pu) : Nat :=
  go c 0
where
  go (c : Code pu) (n : Nat) : Nat :=
    match c with
    | .let (k := k) .. | .sset (k := k) .. | .uset (k := k) .. | .inc (k := k) ..
    | .dec (k := k) .. => go k (n + 1)
    | .jp decl k | .fun decl k _ => go k <| go decl.value n
    | .cases c => c.alts.foldl (init := n+1) fun n alt => go alt.getCode (n+1)
    | .jmp .. => n+1
    | .return .. | unreach .. => n -- `return` & `unreach` have weight zero

/-- Return true iff `c.size ≤ n` -/
partial def Code.sizeLe (c : Code pu) (n : Nat) : Bool :=
  match go c |>.run 0 with
  | .ok .. => true
  | .error .. => false
where
  inc : EStateM Unit Nat Unit := do
    modify (·+1)
    unless (← get) <= n do throw ()

  go (c : Code pu) : EStateM Unit Nat Unit := do
    match c with
    | .let (k := k) .. | .sset (k := k) .. | .uset (k := k) .. | .inc (k := k) ..
    | .dec (k := k) .. => inc; go k
    | .jp decl k | .fun decl k _ => inc; go decl.value; go k
    | .cases c => inc; c.alts.forM fun alt => go alt.getCode
    | .jmp .. => inc
    | .return .. | unreach .. => return ()

partial def Code.forM [Monad m] (c : Code pu) (f : Code pu → m Unit) : m Unit :=
  go c
where
  go (c : Code pu) : m Unit := do
    f c
    match c with
    | .let (k := k) .. | .sset (k := k) .. | .uset (k := k) .. | .inc (k := k) ..
    | .dec (k := k) .. => go k
    | .fun decl k _ | .jp decl k => go decl.value; go k
    | .cases c => c.alts.forM fun alt => go alt.getCode
    | .unreach .. | .return .. | .jmp .. => return ()

partial def Code.instantiateValueLevelParams (code : Code .pure) (levelParams : List Name) (us : List Level) : Code .pure :=
  instCode code
where
  instLevel (u : Level) :=
    u.instantiateParams levelParams us

  instExpr (e : Expr) :=
    e.instantiateLevelParamsNoCache levelParams us

  instParams (ps : Array (Param .pure)) :=
    ps.mapMono fun p => p.updateCore (instExpr p.type)

  instAlt (alt : Alt .pure) :=
    match alt with
    | .default k => alt.updateCode (instCode k)
    | .alt _ ps k _ => alt.updateAlt! (instParams ps) (instCode k)

  instArg (arg : Arg .pure) : Arg .pure :=
    match arg with
    | .type e _ => arg.updateType! (instExpr e)
    | .fvar .. | .erased => arg

  instLetValue (e : LetValue .pure) : LetValue .pure :=
    match e with
    | .const declName vs args _ => e.updateConst! declName (vs.mapMono instLevel) (args.mapMono instArg)
    | .fvar fvarId args => e.updateFVar! fvarId (args.mapMono instArg)
    | .proj .. | .lit .. | .erased => e

  instLetDecl (decl : LetDecl .pure) :=
    decl.updateCore (instExpr decl.type) (instLetValue decl.value)

  instFunDecl (decl : FunDecl .pure) :=
    decl.updateCore (instExpr decl.type) (instParams decl.params) (instCode decl.value)

  instCode (code : Code .pure) :=
    match code with
    | .let decl k => code.updateLet! (instLetDecl decl) (instCode k)
    | .jp decl k | .fun decl k _ => code.updateFun! (instFunDecl decl) (instCode k)
    | .cases c => code.updateCases! (instExpr c.resultType) c.discr (c.alts.mapMono instAlt)
    | .jmp fvarId args => code.updateJmp! fvarId (args.mapMono instArg)
    | .return .. => code
    | .unreach type => code.updateUnreach! (instExpr type)

inductive DeclValue (pu : Purity) where
  | code (code : Code pu)
  | extern (externAttrData : ExternAttrData)
  deriving Inhabited, BEq

partial def DeclValue.size : DeclValue pu → Nat
  | .code c => c.size
  | .extern .. => 0

def DeclValue.mapCode (f : Code pu → Code pu) : DeclValue pu → DeclValue pu :=
  fun
    | .code c => .code (f c)
    | .extern e => .extern e

def DeclValue.mapCodeM [Monad m] (f : Code pu → m (Code pu)) : DeclValue pu → m (DeclValue pu) :=
  fun v => do
    match v with
    | .code c => return .code (← f c)
    | .extern .. => return v

def DeclValue.forCodeM [Monad m] (f : Code pu → m Unit) : DeclValue pu → m Unit :=
  fun v => do
    match v with
    | .code c => f c
    | .extern .. => return ()

def DeclValue.isCodeAndM [Monad m] (v : DeclValue pu) (f : Code pu → m Bool) : m Bool :=
  match v with
  | .code c => f c
  | .extern .. => pure false

/--
The signature of a declaration being processed by the Lean to Lean compiler passes.
-/
structure Signature (pu : Purity) where
  /--
  The name of the declaration from the `Environment` it came from
  -/
  name : Name
  /--
  Universe level parameter names.
  -/
  levelParams : List Name
  /--
  The type of the declaration. Note that this is an erased LCNF type
  instead of the fully dependent one that might have been the original
  type of the declaration in the `Environment`. Furthermore, once in the
  impure staged of LCNF this type is only the return type.
  -/
  type  : Expr
  /--
  Parameters.
  -/
  params : Array (Param pu)
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
  deriving Inhabited, BEq

/--
Declaration being processed by the Lean to Lean compiler passes.
-/
structure Decl (pu : Purity) extends Signature pu where
  /--
  The body of the declaration, usually changes as it progresses
  through compiler passes.
  -/
  value : DeclValue pu
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
  We store the inline attribute at LCNF declarations to make sure we can set them for
  auxiliary declarations created during compilation.
  -/
  inlineAttr? : Option InlineAttributeKind
  deriving Inhabited, BEq

def Decl.size (decl : Decl pu) : Nat :=
  decl.value.size

def Decl.getArity (decl : Decl pu) : Nat :=
  decl.params.size

def Decl.inlineAttr (decl : Decl pu) : Bool :=
  decl.inlineAttr? matches some .inline

def Decl.noinlineAttr (decl : Decl pu) : Bool :=
  decl.inlineAttr? matches some .noinline

def Decl.inlineIfReduceAttr (decl : Decl pu) : Bool :=
  decl.inlineAttr? matches some .inlineIfReduce

def Decl.alwaysInlineAttr (decl : Decl pu) : Bool :=
  decl.inlineAttr? matches some .alwaysInline

/-- Return `true` if the given declaration has been annotated with `[inline]`, `[inline_if_reduce]`, `[macro_inline]`, or `[always_inline]` -/
def Decl.inlineable (decl : Decl pu) : Bool :=
  match decl.inlineAttr? with
  | some .noinline => false
  | some _ => true
  | none => false

def Decl.castPurity! (decl : Decl pu1) (pu2 : Purity) : Decl pu2 :=
  if h : pu1 = pu2 then
    h ▸ decl
  else
    panic! s!"Purity {pu1} does not match {pu2}, this is a bug"

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
def Decl.isCasesOnParam? (decl : Decl pu) : Option Nat :=
  match decl.value with
  | .code c => go c
  | .extern .. => none
where
  go {pu : Purity} (code : Code pu) : Option Nat :=
    match code with
    | .let _ k | .jp _ k | .fun _ k _ => go k
    | .cases c => decl.params.findIdx? fun param => param.fvarId == c.discr
    | _ => none

def Decl.instantiateTypeLevelParams (decl : Decl pu) (us : List Level) : Expr :=
  decl.type.instantiateLevelParamsNoCache decl.levelParams us

def Decl.instantiateParamsLevelParams (decl : Decl pu) (us : List Level) : Array (Param pu) :=
  decl.params.mapMono fun param => param.updateCore (param.type.instantiateLevelParamsNoCache decl.levelParams us)

/--
Return `true` if the arrow type contains an instance implicit argument.
-/
def hasLocalInst (type : Expr) : CoreM Bool := do
  match type with
  | .forallE _ d b bi =>
    (pure bi.isInstImplicit) <||>
    ((pure bi.isImplicit) <&&> (pure (← isArrowClass? d).isSome)) <||>
    hasLocalInst b
  | _ => return false

/--
Return `true` if `decl` is supposed to be inlined/specialized.
-/
def Decl.isTemplateLike (decl : Decl pu) : CoreM Bool := do
  let env ← getEnv
  if ← hasLocalInst decl.type then
    return true -- `decl` applications will be specialized
  else if (← isInstanceReducible decl.name) then
    return true -- `decl` is "fuel" for code specialization
  else if decl.inlineable || hasSpecializeAttribute env decl.name then
    return true -- `decl` is going to be inlined or specialized
  else
    return false

private partial def collectType (e : Expr) : FVarIdHashSet → FVarIdHashSet :=
  if e.hasFVar then
    match e with
    | .forallE _ d b _ => collectType b ∘ collectType d
    | .lam _ d b _     => collectType b ∘ collectType d
    | .app f a         => collectType f ∘ collectType a
    | .fvar fvarId     => fun s => s.insert fvarId
    | .mdata _ b       => collectType b
    | .proj .. | .letE .. => unreachable!
    | _                => id
  else
    id

private def collectArg (arg : Arg pu) (s : FVarIdHashSet) : FVarIdHashSet :=
  match arg with
  | .erased => s
  | .fvar fvarId => s.insert fvarId
  | .type e _ => collectType e s

private def collectArgs (args : Array (Arg pu)) (s : FVarIdHashSet) : FVarIdHashSet :=
  args.foldl (init := s) fun s arg => collectArg arg s

private def collectLetValue (e : LetValue pu) (s : FVarIdHashSet) : FVarIdHashSet :=
  match e with
  | .fvar fvarId args => collectArgs args <| s.insert fvarId
  | .const _ _ args _ | .pap _ args _ | .fap _ args _ | .ctor _ args _  => collectArgs args s
  | .proj _ _ fvarId _ | .sproj _ _ fvarId _ | .uproj _ fvarId _ | .oproj _ fvarId _
  | .reset _ fvarId _  | .box _ fvarId _ | .unbox fvarId _ => s.insert fvarId
  | .lit .. | .erased => s
  | .reuse fvarId _ _ args _ => collectArgs args <| s.insert fvarId

private partial def collectParams (ps : Array (Param pu)) (s : FVarIdHashSet) : FVarIdHashSet :=
  ps.foldl (init := s) fun s p => collectType p.type s

mutual
partial def FunDecl.collectUsed (decl : FunDecl pu) (s : FVarIdHashSet := {}) : FVarIdHashSet :=
  decl.value.collectUsed <| collectParams decl.params <| collectType decl.type s

partial def Code.collectUsed (code : Code pu) (s : FVarIdHashSet := {}) : FVarIdHashSet :=
  match code with
  | .let decl k => k.collectUsed <| collectLetValue decl.value <| collectType decl.type s
  | .jp decl k | .fun decl k _ => k.collectUsed <| decl.collectUsed s
  | .cases c =>
    let s := s.insert c.discr
    let s := collectType c.resultType s
    c.alts.foldl (init := s) fun s alt =>
      match alt with
      | .default k | .ctorAlt _ k _  => k.collectUsed s
      | .alt _ ps k _ => k.collectUsed <| collectParams ps s
  | .return fvarId => s.insert fvarId
  | .unreach type => collectType type s
  | .jmp fvarId args => collectArgs args <| s.insert fvarId
  | .sset var _ _ y _ k _ | .uset var _ y k _ =>
    let s := s.insert var
    let s := s.insert y
    k.collectUsed s
  | .inc (fvarId := fvarId) (k := k) .. | .dec (fvarId := fvarId) (k := k) .. =>
    k.collectUsed <| s.insert fvarId
end

@[inline] def collectUsedAtExpr (s : FVarIdHashSet) (e : Expr) : FVarIdHashSet :=
  collectType e s

def CodeDecl.collectUsed (codeDecl : CodeDecl pu) (s : FVarIdHashSet := ∅) : FVarIdHashSet :=
  match codeDecl with
  | .let decl => collectLetValue decl.value <| collectType decl.type s
  | .jp decl | .fun decl _ => decl.collectUsed s
  | .sset (var := var) (y := y) .. | .uset (var := var) (y := y) .. => s.insert var |>.insert y
  | .inc (fvarId := fvarId) .. | .dec (fvarId := fvarId) .. => s.insert fvarId

/--
Traverse the given block of potentially mutually recursive functions
and mark a declaration `f` as recursive if there is an application
`f ...` in the block.
This is an overapproximation, and relies on the fact that our frontend
computes strongly connected components.
See comment at `recursive` field.
-/
partial def markRecDecls (decls : Array (Decl pu)) : Array (Decl pu)  :=
  let (_, isRec) := go |>.run {}
  decls.map fun decl =>
    if isRec.contains decl.name then
      { decl with recursive := true }
    else
      decl
where
  visit {pu : Purity} (code : Code pu) : StateM NameSet Unit := do
    match code with
    | .jp decl k | .fun decl k _ => visit decl.value; visit k
    | .cases c => c.alts.forM fun alt => visit alt.getCode
    | .unreach .. | .jmp .. | .return .. => return ()
    | .let decl k =>
      match decl.value with
      | .const declName .. | .fap declName .. | .pap declName .. =>
        if decls.any (·.name == declName) then
          modify fun s => s.insert declName
      | _ => pure ()
      visit k
    | .uset (k := k) .. | .sset (k := k) .. | .inc (k := k) .. | .dec (k := k) .. => visit k

  go : StateM NameSet Unit :=
    decls.forM (·.value.forCodeM visit)

def instantiateRangeArgs (e : Expr) (beginIdx endIdx : Nat) (args : Array (Arg pu)) : Expr :=
  if !e.hasLooseBVars then
    e
  else
    e.instantiateRange beginIdx endIdx (args.map (·.toExpr))

def instantiateRevRangeArgs (e : Expr) (beginIdx endIdx : Nat) (args : Array (Arg pu)) : Expr :=
  if !e.hasLooseBVars then
    e
  else
    e.instantiateRevRange beginIdx endIdx (args.map (·.toExpr))

def findExtEntry? [Inhabited σ] (env : Environment) (ext : PersistentEnvExtension α β σ) (declName : Name)
    (findAtSorted? : Array α → Name → Option α')
    (findInState? : σ → Name → Option α') : Option α' :=
  (env.getModuleIdxFor? declName).bind (fun modIdx =>
    --findAtSorted? (ext.getModuleEntries env modIdx) declName <|>
    -- When
    guard (getIRPhases env declName != .runtime) *> findAtSorted? (ext.getModuleIREntries env modIdx) declName)
  <|> findInState? (ext.getState env) declName

end Lean.Compiler.LCNF
