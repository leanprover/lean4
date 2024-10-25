/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr

namespace Lean
/--
Reducibility hints are used in the convertibility checker.
When trying to solve a constraint such a

           (f ...) =?= (g ...)

where f and g are definitions, the checker has to decide which one will be unfolded.
  If      f (g) is opaque,     then g (f) is unfolded if it is also not marked as opaque,
  Else if f (g) is abbrev,     then f (g) is unfolded if g (f) is also not marked as abbrev,
  Else if f and g are regular, then we unfold the one with the biggest definitional height.
  Otherwise both are unfolded.

The arguments of the `regular` Constructor are: the definitional height and the flag `selfOpt`.

The definitional height is by default computed by the kernel. It only takes into account
other regular definitions used in a definition. When creating declarations using meta-programming,
we can specify the definitional depth manually.

Remark: the hint only affects performance. None of the hints prevent the kernel from unfolding a
declaration during Type checking.

Remark: the ReducibilityHints are not related to the attributes: reducible/irrelevance/semireducible.
These attributes are used by the Elaborator. The ReducibilityHints are used by the kernel (and Elaborator).
Moreover, the ReducibilityHints cannot be changed after a declaration is added to the kernel. -/
inductive ReducibilityHints where
  | opaque  : ReducibilityHints
  | abbrev  : ReducibilityHints
  | regular : UInt32 → ReducibilityHints
  deriving Inhabited, BEq

@[export lean_mk_reducibility_hints_regular]
def mkReducibilityHintsRegularEx (h : UInt32) : ReducibilityHints :=
  ReducibilityHints.regular h

@[export lean_reducibility_hints_get_height]
def ReducibilityHints.getHeightEx (h : ReducibilityHints) : UInt32 :=
  match h with
  | ReducibilityHints.regular h => h
  | _ => 0

namespace ReducibilityHints

-- Recall that if `lt h₁ h₂`, we want to reduce declaration associated with `h₁`.
def lt : ReducibilityHints → ReducibilityHints → Bool
  | .abbrev,     .abbrev     => false
  | .abbrev,     _           => true
  | .regular d₁, .regular d₂ => d₁ > d₂
  | .regular _,  .opaque     => true
  | _,           _           => false

protected def compare : ReducibilityHints → ReducibilityHints → Ordering
  | .abbrev,     .abbrev     => .eq
  | .abbrev,     _           => .lt
  | .regular _,  .abbrev     => .gt
  | .regular d₁, .regular d₂ => Ord.compare d₂ d₁
  | .regular _,  .opaque     => .lt
  | .opaque,     .opaque     => .eq
  | .opaque,     _           => .gt

instance : Ord ReducibilityHints where
  compare := ReducibilityHints.compare

def isAbbrev : ReducibilityHints → Bool
  | .abbrev => true
  | _       => false

def isRegular : ReducibilityHints → Bool
  | regular .. => true
  | _          => false

end ReducibilityHints

/-- Base structure for `AxiomVal`, `DefinitionVal`, `TheoremVal`, `InductiveVal`, `ConstructorVal`, `RecursorVal` and `QuotVal`. -/
structure ConstantVal where
  name : Name
  levelParams : List Name
  type : Expr
  deriving Inhabited, BEq

structure AxiomVal extends ConstantVal where
  isUnsafe : Bool
  deriving Inhabited, BEq

@[export lean_mk_axiom_val]
def mkAxiomValEx (name : Name) (levelParams : List Name) (type : Expr) (isUnsafe : Bool) : AxiomVal := {
  name := name,
  levelParams := levelParams,
  type := type,
  isUnsafe := isUnsafe
}

@[export lean_axiom_val_is_unsafe] def AxiomVal.isUnsafeEx (v : AxiomVal) : Bool :=
  v.isUnsafe

inductive DefinitionSafety where
  | «unsafe» | safe | «partial»
  deriving Inhabited, BEq, Repr

structure DefinitionVal extends ConstantVal where
  value  : Expr
  hints  : ReducibilityHints
  safety : DefinitionSafety
  /--
    List of all (including this one) declarations in the same mutual block.
    Note that this information is not used by the kernel, and is only used
    to save the information provided by the user when using mutual blocks.
    Recall that the Lean kernel does not support recursive definitions and they
    are compiled using recursors and `WellFounded.fix`.
  -/
  all : List Name := [name]
  deriving Inhabited, BEq

@[export lean_mk_definition_val]
def mkDefinitionValEx (name : Name) (levelParams : List Name) (type : Expr) (value : Expr) (hints : ReducibilityHints) (safety : DefinitionSafety) (all : List Name) : DefinitionVal := {
  name, levelParams, type, hints, safety, value, all
}

@[export lean_definition_val_get_safety] def DefinitionVal.getSafetyEx (v : DefinitionVal) : DefinitionSafety :=
  v.safety

structure TheoremVal extends ConstantVal where
  value : Expr
  /--
    List of all (including this one) declarations in the same mutual block.
    See comment at `DefinitionVal.all`. -/
  all : List Name := [name]
  deriving Inhabited, BEq

@[export lean_mk_theorem_val]
def mkTheoremValEx (name : Name) (levelParams : List Name) (type : Expr) (value : Expr) (all : List Name) : TheoremVal := {
  name, levelParams, type, value, all
}

/-- Value for an opaque constant declaration `opaque x : t := e` -/
structure OpaqueVal extends ConstantVal where
  value : Expr
  isUnsafe : Bool
  /--
    List of all (including this one) declarations in the same mutual block.
    See comment at `DefinitionVal.all`. -/
  all : List Name := [name]
  deriving Inhabited, BEq

@[export lean_mk_opaque_val]
def mkOpaqueValEx (name : Name) (levelParams : List Name) (type : Expr) (value : Expr) (isUnsafe : Bool) (all : List Name) : OpaqueVal := {
  name, levelParams, type, value, isUnsafe, all
}

@[export lean_opaque_val_is_unsafe] def OpaqueVal.isUnsafeEx (v : OpaqueVal) : Bool :=
  v.isUnsafe

structure Constructor where
  name : Name
  type : Expr
  deriving Inhabited, BEq

structure InductiveType where
  name : Name
  type : Expr
  ctors : List Constructor
  deriving Inhabited, BEq

/-- Declaration object that can be sent to the kernel. -/
inductive Declaration where
  | axiomDecl       (val : AxiomVal)
  | defnDecl        (val : DefinitionVal)
  | thmDecl         (val : TheoremVal)
  | opaqueDecl      (val : OpaqueVal)
  | quotDecl
  | mutualDefnDecl  (defns : List DefinitionVal) -- All definitions must be marked as `unsafe` or `partial`
  | inductDecl      (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
  deriving Inhabited, BEq

@[export lean_mk_inductive_decl]
def mkInductiveDeclEs (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) : Declaration :=
  Declaration.inductDecl lparams nparams types isUnsafe

@[export lean_is_unsafe_inductive_decl]
def Declaration.isUnsafeInductiveDeclEx : Declaration → Bool
  | Declaration.inductDecl _ _ _ isUnsafe => isUnsafe
  | _ => false

def Declaration.definitionVal! : Declaration → DefinitionVal
  | .defnDecl val => val
  | _ => panic! "Expected a `Declaration.defnDecl`."

/--
Returns all top-level names to be defined by adding this declaration to the environment. This does
not include auxiliary definitions such as projections.
-/
def Declaration.getNames : Declaration → List Name
  | .axiomDecl val          => [val.name]
  | .defnDecl val           => [val.name]
  | .thmDecl val            => [val.name]
  | .opaqueDecl val         => [val.name]
  | .quotDecl               => [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  | .mutualDefnDecl defns   => defns.map (·.name)
  | .inductDecl _ _ types _ => types.map (·.name)

@[specialize] def Declaration.foldExprM {α} {m : Type → Type} [Monad m] (d : Declaration) (f : α → Expr → m α) (a : α) : m α :=
  match d with
  | Declaration.quotDecl                                        => pure a
  | Declaration.axiomDecl { type := type, .. }                  => f a type
  | Declaration.defnDecl { type := type, value := value, .. }   => do let a ← f a type; f a value
  | Declaration.opaqueDecl { type := type, value := value, .. } => do let a ← f a type; f a value
  | Declaration.thmDecl { type := type, value := value, .. }    => do let a ← f a type; f a value
  | Declaration.mutualDefnDecl vals                             => vals.foldlM (fun a v => do let a ← f a v.type; f a v.value) a
  | Declaration.inductDecl _ _ inductTypes _                    =>
    inductTypes.foldlM
      (fun a inductType => do
        let a ← f a inductType.type
        inductType.ctors.foldlM (fun a ctor => f a ctor.type) a)
      a

@[inline] def Declaration.forExprM {m : Type → Type} [Monad m] (d : Declaration) (f : Expr → m Unit) : m Unit :=
  d.foldExprM (fun _ a => f a) ()

/-- The kernel compiles (mutual) inductive declarations (see `inductiveDecls`) into a set of
    - `Declaration.inductDecl` (for each inductive datatype in the mutual Declaration),
    - `Declaration.ctorDecl` (for each Constructor in the mutual Declaration),
    - `Declaration.recDecl` (automatically generated recursors).

    This data is used to implement iota-reduction efficiently and compile nested inductive
    declarations.

    A series of checks are performed by the kernel to check whether a `inductiveDecls`
    is valid or not. -/
structure InductiveVal extends ConstantVal where
  /-- Number of parameters. A parameter is an argument to the defined type that is fixed over constructors.
  An example of this is the `α : Type` argument in the vector constructors
  `nil : Vector α 0` and `cons : α → Vector α n → Vector α (n+1)`.

  The intuition is that the inductive type must exhibit _parametric polymorphism_ over the inductive
  parameter, as opposed to _ad-hoc polymorphism_.
  -/
  numParams : Nat
  /-- Number of indices. An index is an argument that varies over constructors.

  An example of this is the `n : Nat` argument in the vector constructor `cons : α → Vector α n → Vector α (n+1)`.
  -/
  numIndices : Nat
  /-- List of all (including this one) inductive datatypes in the mutual declaration containing this one -/
  all : List Name
  /-- List of the names of the constructors for this inductive datatype. -/
  ctors : List Name
  /-- Number of auxiliary data types produced from nested occurrences.
  An inductive definition `T` is nested when there is a constructor with an argument `x : F T`,
   where `F : Type → Type` is some suitably behaved (ie strictly positive) function (Eg `Array T`, `List T`, `T × T`, ...).  -/
  numNested : Nat
  /-- `true` when recursive (that is, the inductive type appears as an argument in a constructor). -/
  isRec : Bool
  /-- Whether the definition is flagged as unsafe. -/
  isUnsafe : Bool
  /-- An inductive type is called reflexive if it has at least one constructor that takes as an argument a function returning the
  same type we are defining.
  Consider the type:
  ```
  inductive WideTree where
  | branch: (Nat -> WideTree) -> WideTree
  | leaf: WideTree
  ```
  this is reflexive due to the presence of the `branch : (Nat -> WideTree) -> WideTree` constructor.

  See also: 'Inductive Definitions in the system Coq Rules and Properties' by Christine Paulin-Mohring
  Section 2.2, Definition 3
  -/
  isReflexive : Bool

  deriving Inhabited

@[export lean_mk_inductive_val]
def mkInductiveValEx (name : Name) (levelParams : List Name) (type : Expr) (numParams numIndices : Nat)
    (all ctors : List Name) (numNested : Nat) (isRec isUnsafe isReflexive : Bool) : InductiveVal := {
  name := name
  levelParams := levelParams
  type := type
  numParams := numParams
  numIndices := numIndices
  all := all
  ctors := ctors
  numNested := numNested
  isRec := isRec
  isUnsafe := isUnsafe
  isReflexive := isReflexive
}

@[export lean_inductive_val_is_rec] def InductiveVal.isRecEx (v : InductiveVal) : Bool := v.isRec
@[export lean_inductive_val_is_unsafe] def InductiveVal.isUnsafeEx (v : InductiveVal) : Bool := v.isUnsafe
@[export lean_inductive_val_is_reflexive] def InductiveVal.isReflexiveEx (v : InductiveVal) : Bool := v.isReflexive

def InductiveVal.numCtors (v : InductiveVal) : Nat := v.ctors.length
def InductiveVal.isNested (v : InductiveVal) : Bool := v.numNested > 0
def InductiveVal.numTypeFormers (v : InductiveVal) : Nat := v.all.length + v.numNested

structure ConstructorVal extends ConstantVal where
  /-- Inductive type this constructor is a member of -/
  induct  : Name
  /-- Constructor index (i.e., Position in the inductive declaration) -/
  cidx    : Nat
  /-- Number of parameters in inductive datatype. -/
  numParams : Nat
  /-- Number of fields (i.e., arity - nparams) -/
  numFields : Nat
  isUnsafe : Bool
  deriving Inhabited, BEq

@[export lean_mk_constructor_val]
def mkConstructorValEx (name : Name) (levelParams : List Name) (type : Expr) (induct : Name) (cidx numParams numFields : Nat) (isUnsafe : Bool) : ConstructorVal := {
  name := name,
  levelParams := levelParams,
  type := type,
  induct := induct,
  cidx := cidx,
  numParams := numParams,
  numFields := numFields,
  isUnsafe := isUnsafe
}

@[export lean_constructor_val_is_unsafe] def ConstructorVal.isUnsafeEx (v : ConstructorVal) : Bool := v.isUnsafe

/-- Information for reducing a recursor -/
structure RecursorRule where
  /-- Reduction rule for this Constructor -/
  ctor : Name
  /-- Number of fields (i.e., without counting inductive datatype parameters) -/
  nfields : Nat
  /-- Right hand side of the reduction rule -/
  rhs : Expr
  deriving Inhabited, BEq

structure RecursorVal extends ConstantVal where
  /-- List of all inductive datatypes in the mutual declaration that generated this recursor -/
  all : List Name
  /-- Number of parameters -/
  numParams : Nat
  /-- Number of indices -/
  numIndices : Nat
  /-- Number of motives -/
  numMotives : Nat
  /-- Number of minor premises -/
  numMinors : Nat
  /-- A reduction for each Constructor -/
  rules : List RecursorRule
  /-- It supports K-like reduction.
  A recursor is said to support K-like reduction if one can assume it behaves
  like `Eq` under axiom `K` --- that is, it has one constructor, the constructor has 0 arguments,
  and it is an inductive predicate (ie, it lives in Prop).

  Examples of inductives with K-like reduction is `Eq`, `Acc`, and `And.intro`.
  Non-examples are `exists` (where the constructor has arguments) and
    `Or.intro` (which has multiple constructors).
  -/
  k : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq

@[export lean_mk_recursor_val]
def mkRecursorValEx (name : Name) (levelParams : List Name) (type : Expr) (all : List Name) (numParams numIndices numMotives numMinors : Nat)
    (rules : List RecursorRule) (k isUnsafe : Bool) : RecursorVal := {
  name := name, levelParams := levelParams, type := type, all := all, numParams := numParams, numIndices := numIndices,
  numMotives := numMotives, numMinors := numMinors, rules := rules, k := k, isUnsafe := isUnsafe
}

@[export lean_recursor_k] def RecursorVal.kEx (v : RecursorVal) : Bool := v.k
@[export lean_recursor_is_unsafe] def RecursorVal.isUnsafeEx (v : RecursorVal) : Bool := v.isUnsafe

def RecursorVal.getMajorIdx (v : RecursorVal) : Nat :=
  v.numParams + v.numMotives + v.numMinors + v.numIndices

def RecursorVal.getFirstIndexIdx (v : RecursorVal) : Nat :=
  v.numParams + v.numMotives + v.numMinors

def RecursorVal.getFirstMinorIdx (v : RecursorVal) : Nat :=
  v.numParams + v.numMotives

/-- The inductive type of the major argument of the recursor. -/
def RecursorVal.getMajorInduct (v : RecursorVal) : Name :=
  go v.getMajorIdx v.type
where
  go
  | 0, e => e.bindingDomain!.getAppFn.constName!
  | n+1, e => go n e.bindingBody!

inductive QuotKind where
  | type  -- `Quot`
  | ctor  -- `Quot.mk`
  | lift  -- `Quot.lift`
  | ind   -- `Quot.ind`
  deriving Inhabited

structure QuotVal extends ConstantVal where
  kind : QuotKind
  deriving Inhabited

@[export lean_mk_quot_val]
def mkQuotValEx (name : Name) (levelParams : List Name) (type : Expr) (kind : QuotKind) : QuotVal := {
  name := name, levelParams := levelParams, type := type, kind := kind
}

@[export lean_quot_val_kind] def QuotVal.kindEx (v : QuotVal) : QuotKind := v.kind

/-- Information associated with constant declarations. -/
inductive ConstantInfo where
  | axiomInfo    (val : AxiomVal)
  | defnInfo     (val : DefinitionVal)
  | thmInfo      (val : TheoremVal)
  | opaqueInfo   (val : OpaqueVal)
  | quotInfo     (val : QuotVal)
  | inductInfo   (val : InductiveVal)
  | ctorInfo     (val : ConstructorVal)
  | recInfo      (val : RecursorVal)
  deriving Inhabited

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | defnInfo     {toConstantVal := d, ..} => d
  | axiomInfo    {toConstantVal := d, ..} => d
  | thmInfo      {toConstantVal := d, ..} => d
  | opaqueInfo   {toConstantVal := d, ..} => d
  | quotInfo     {toConstantVal := d, ..} => d
  | inductInfo   {toConstantVal := d, ..} => d
  | ctorInfo     {toConstantVal := d, ..} => d
  | recInfo      {toConstantVal := d, ..} => d

def isUnsafe : ConstantInfo → Bool
  | defnInfo   v => v.safety == .unsafe
  | axiomInfo  v => v.isUnsafe
  | thmInfo    _ => false
  | opaqueInfo v => v.isUnsafe
  | quotInfo   _ => false
  | inductInfo v => v.isUnsafe
  | ctorInfo   v => v.isUnsafe
  | recInfo    v => v.isUnsafe

def isPartial : ConstantInfo → Bool
  | defnInfo v => v.safety == .partial
  | _ => false

def name (d : ConstantInfo) : Name :=
  d.toConstantVal.name

def levelParams (d : ConstantInfo) : List Name :=
  d.toConstantVal.levelParams

def numLevelParams (d : ConstantInfo) : Nat :=
  d.levelParams.length

def type (d : ConstantInfo) : Expr :=
  d.toConstantVal.type

def value? : ConstantInfo → Option Expr
  | defnInfo {value := r, ..} => some r
  | thmInfo  {value := r, ..} => some r
  | _                         => none

def hasValue : ConstantInfo → Bool
  | defnInfo _ => true
  | thmInfo  _ => true
  | _                         => false

def value! : ConstantInfo → Expr
  | defnInfo {value := r, ..} => r
  | thmInfo  {value := r, ..} => r
  | _                         => panic! "declaration with value expected"

def hints : ConstantInfo → ReducibilityHints
  | defnInfo {hints := r, ..} => r
  | _                         => ReducibilityHints.opaque

def isCtor : ConstantInfo → Bool
  | ctorInfo _ => true
  | _          => false

def isInductive : ConstantInfo → Bool
  | inductInfo _ => true
  | _            => false

def isTheorem : ConstantInfo → Bool
  | thmInfo _ => true
  | _         => false

def inductiveVal! : ConstantInfo → InductiveVal
  | .inductInfo val => val
  | _ => panic! "Expected a `ConstantInfo.inductInfo`."

/--
  List of all (including this one) declarations in the same mutual block.
-/
def all : ConstantInfo → List Name
  | inductInfo val => val.all
  | defnInfo val   => val.all
  | thmInfo val    => val.all
  | opaqueInfo val => val.all
  | info           => [info.name]

end ConstantInfo

def mkRecName (declName : Name) : Name :=
  Name.mkStr declName "rec"

end Lean
