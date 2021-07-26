/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
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
  | opaque   : ReducibilityHints
  | «abbrev» : ReducibilityHints
  | regular  : UInt32 → ReducibilityHints
  deriving Inhabited

@[export lean_mk_reducibility_hints_regular]
def mkReducibilityHintsRegularEx (h : UInt32) : ReducibilityHints :=
  ReducibilityHints.regular h

@[export lean_reducibility_hints_get_height]
def ReducibilityHints.getHeightEx (h : ReducibilityHints) : UInt32 :=
  match h with
  | ReducibilityHints.regular h => h
  | _ => 0

namespace ReducibilityHints

def lt : ReducibilityHints → ReducibilityHints → Bool
  | «abbrev»,   «abbrev»   => false
  | «abbrev»,   _          => true
  | regular d₁, regular d₂ => d₁ < d₂
  | regular _,  opaque     => true
  | _,          _          => false

def isAbbrev : ReducibilityHints → Bool
  | «abbrev» => true
  | _        => false

def isRegular : ReducibilityHints → Bool
  | regular .. => true
  | _          => false

end ReducibilityHints

/-- Base structure for `AxiomVal`, `DefinitionVal`, `TheoremVal`, `InductiveVal`, `ConstructorVal`, `RecursorVal` and `QuotVal`. -/
structure ConstantVal where
  name : Name
  levelParams : List Name
  type : Expr
  deriving Inhabited

structure AxiomVal extends ConstantVal where
  isUnsafe : Bool
  deriving Inhabited

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
  deriving Inhabited

@[export lean_mk_definition_val]
def mkDefinitionValEx (name : Name) (levelParams : List Name) (type : Expr) (val : Expr) (hints : ReducibilityHints) (safety : DefinitionSafety) : DefinitionVal := {
  name := name,
  levelParams := levelParams,
  type := type,
  value := val,
  hints := hints,
  safety := safety
}

@[export lean_definition_val_get_safety] def DefinitionVal.getSafetyEx (v : DefinitionVal) : DefinitionSafety :=
  v.safety

structure TheoremVal extends ConstantVal where
  value : Expr
  deriving Inhabited

/- Value for an opaque constant declaration `constant x : t := e` -/
structure OpaqueVal extends ConstantVal where
  value : Expr
  isUnsafe : Bool
  deriving Inhabited

@[export lean_mk_opaque_val]
def mkOpaqueValEx (name : Name) (levelParams : List Name) (type : Expr) (val : Expr) (isUnsafe : Bool) : OpaqueVal := {
  name := name,
  levelParams := levelParams,
  type := type,
  value := val,
  isUnsafe := isUnsafe
}

@[export lean_opaque_val_is_unsafe] def OpaqueVal.isUnsafeEx (v : OpaqueVal) : Bool :=
  v.isUnsafe

structure Constructor where
  name : Name
  type : Expr
  deriving Inhabited

structure InductiveType where
  name : Name
  type : Expr
  ctors : List Constructor
  deriving Inhabited

/-- Declaration object that can be sent to the kernel. -/
inductive Declaration where
  | axiomDecl       (val : AxiomVal)
  | defnDecl        (val : DefinitionVal)
  | thmDecl         (val : TheoremVal)
  | opaqueDecl      (val : OpaqueVal)
  | quotDecl
  | mutualDefnDecl  (defns : List DefinitionVal) -- All definitions must be marked as `unsafe` or `partial`
  | inductDecl      (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
  deriving Inhabited

@[export lean_mk_inductive_decl]
def mkInductiveDeclEs (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) : Declaration :=
  Declaration.inductDecl lparams nparams types isUnsafe

@[export lean_is_unsafe_inductive_decl]
def Declaration.isUnsafeInductiveDeclEx : Declaration → Bool
  | Declaration.inductDecl _ _ _ isUnsafe => isUnsafe
  | _ => false

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
  numParams : Nat     -- Number of parameters
  numIndices : Nat    -- Number of indices
  all : List Name     -- List of all (including this one) inductive datatypes in the mutual declaration containing this one
  ctors : List Name   -- List of all constructors for this inductive datatype
  isRec : Bool        -- `true` Iff it is recursive
  isUnsafe : Bool
  isReflexive : Bool
  isNested : Bool
  deriving Inhabited

@[export lean_mk_inductive_val]
def mkInductiveValEx (name : Name) (levelParams : List Name) (type : Expr) (numParams numIndices : Nat)
    (all ctors : List Name) (isRec isUnsafe isReflexive isNested : Bool) : InductiveVal := {
  name := name
  levelParams := levelParams
  type := type
  numParams := numParams
  numIndices := numIndices
  all := all
  ctors := ctors
  isRec := isRec
  isUnsafe := isUnsafe
  isReflexive := isReflexive
  isNested := isNested
}

@[export lean_inductive_val_is_rec] def InductiveVal.isRecEx (v : InductiveVal) : Bool := v.isRec
@[export lean_inductive_val_is_unsafe] def InductiveVal.isUnsafeEx (v : InductiveVal) : Bool := v.isUnsafe
@[export lean_inductive_val_is_reflexive] def InductiveVal.isReflexiveEx (v : InductiveVal) : Bool := v.isReflexive
@[export lean_inductive_val_is_nested] def InductiveVal.isNestedEx (v : InductiveVal) : Bool := v.isNested

def InductiveVal.nctors (v : InductiveVal) : Nat := v.ctors.length

structure ConstructorVal extends ConstantVal where
  induct  : Name    -- Inductive Type this Constructor is a member of
  cidx    : Nat     -- Constructor index (i.e., Position in the inductive declaration)
  numParams : Nat   -- Number of parameters in inductive datatype `induct`
  numFields : Nat   -- Number of fields (i.e., arity - nparams)
  isUnsafe : Bool
  deriving Inhabited

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
  ctor : Name   -- Reduction rule for this Constructor
  nfields : Nat -- Number of fields (i.e., without counting inductive datatype parameters)
  rhs : Expr    -- Right hand side of the reduction rule
  deriving Inhabited

structure RecursorVal extends ConstantVal where
  all : List Name              -- List of all inductive datatypes in the mutual declaration that generated this recursor
  numParams : Nat              -- Number of parameters
  numIndices : Nat             -- Number of indices
  numMotives : Nat             -- Number of motives
  numMinors : Nat              -- Number of minor premises
  rules : List RecursorRule    -- A reduction for each Constructor
  k : Bool                     -- It supports K-like reduction
  isUnsafe : Bool
  deriving Inhabited

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

def RecursorVal.getInduct (v : RecursorVal) : Name :=
  v.name.getPrefix

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
  | defnInfo   v => v.safety == DefinitionSafety.unsafe
  | axiomInfo  v => v.isUnsafe
  | thmInfo    v => false
  | opaqueInfo v => v.isUnsafe
  | quotInfo   v => false
  | inductInfo v => v.isUnsafe
  | ctorInfo   v => v.isUnsafe
  | recInfo    v => v.isUnsafe

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
  | defnInfo {value := r, ..} => true
  | thmInfo  {value := r, ..} => true
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

@[extern "lean_instantiate_type_lparams"]
constant instantiateTypeLevelParams (c : @& ConstantInfo) (ls : @& List Level) : Expr

@[extern "lean_instantiate_value_lparams"]
constant instantiateValueLevelParams (c : @& ConstantInfo) (ls : @& List Level) : Expr

end ConstantInfo

def mkRecName (declName : Name) : Name :=
  Name.mkStr declName "rec"

end Lean
