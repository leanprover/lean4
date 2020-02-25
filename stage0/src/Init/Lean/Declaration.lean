/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr

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
inductive ReducibilityHints
| opaque   : ReducibilityHints
| «abbrev» : ReducibilityHints
| regular  : UInt32 → ReducibilityHints

@[export lean_mk_reducibility_hints_regular]
def mkReducibilityHintsRegularEx (h : UInt32) : ReducibilityHints := ReducibilityHints.regular h
@[export lean_reducibility_hints_get_height]
def ReducibilityHints.getHeightEx (h : ReducibilityHints) : UInt32 :=
match h with
| ReducibilityHints.regular h => h
| _ => 0

namespace ReducibilityHints

instance : Inhabited ReducibilityHints := ⟨opaque⟩

def lt : ReducibilityHints → ReducibilityHints → Bool
| «abbrev»,   «abbrev»   => false
| «abbrev»,   _          => true
| regular d₁, regular d₂ => d₁ < d₂
| regular _,  opaque     => true
| _,          _          => false

end ReducibilityHints

/-- Base structure for `AxiomVal`, `DefinitionVal`, `TheoremVal`, `InductiveVal`, `ConstructorVal`, `RecursorVal` and `QuotVal`. -/
structure ConstantVal :=
(name : Name) (lparams : List Name) (type : Expr)

instance ConstantVal.inhabited : Inhabited ConstantVal := ⟨{ name := arbitrary _, lparams := arbitrary _, type := arbitrary _ }⟩

structure AxiomVal extends ConstantVal :=
(isUnsafe : Bool)

@[export lean_mk_axiom_val]
def mkAxiomValEx (name : Name) (lparams : List Name) (type : Expr) (isUnsafe : Bool) : AxiomVal :=
{ name := name, lparams := lparams, type := type, isUnsafe := isUnsafe }
@[export lean_axiom_val_is_unsafe] def AxiomVal.isUnsafeEx (v : AxiomVal) : Bool := v.isUnsafe

structure DefinitionVal extends ConstantVal :=
(value : Expr) (hints : ReducibilityHints) (isUnsafe : Bool)

@[export lean_mk_definition_val]
def mkDefinitionValEx (name : Name) (lparams : List Name) (type : Expr) (val : Expr) (hints : ReducibilityHints) (isUnsafe : Bool) : DefinitionVal :=
{ name := name, lparams := lparams, type := type, value := val, hints := hints, isUnsafe := isUnsafe }
@[export lean_definition_val_is_unsafe] def DefinitionVal.isUnsafeEx (v : DefinitionVal) : Bool := v.isUnsafe

structure TheoremVal extends ConstantVal :=
(value : Task Expr)

/- Value for an opaque constant declaration `constant x : t := e` -/
structure OpaqueVal extends ConstantVal :=
(value : Expr) (isUnsafe : Bool)

@[export lean_mk_opaque_val]
def mkOpaqueValEx (name : Name) (lparams : List Name) (type : Expr) (val : Expr) (isUnsafe : Bool) : OpaqueVal :=
{ name := name, lparams := lparams, type := type, value := val, isUnsafe := isUnsafe }
@[export lean_opaque_val_is_unsafe] def OpaqueVal.isUnsafeEx (v : OpaqueVal) : Bool := v.isUnsafe

structure Constructor :=
(name : Name) (type : Expr)

structure InductiveType :=
(name : Name) (type : Expr) (ctors : List Constructor)

/-- Declaration object that can be sent to the kernel. -/
inductive Declaration
| axiomDecl       (val : AxiomVal)
| defnDecl        (val : DefinitionVal)
| thmDecl         (val : TheoremVal)
| opaqueDecl      (val : OpaqueVal)
| quotDecl
| mutualDefnDecl  (defns : List DefinitionVal) -- All definitions must be marked as `unsafe`
| inductDecl      (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)

@[export lean_mk_inductive_decl]
def mkInductiveDeclEs (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) : Declaration :=
Declaration.inductDecl lparams nparams types isUnsafe
@[export lean_is_unsafe_inductive_decl]
def Declaration.isUnsafeInductiveDeclEx : Declaration → Bool
| Declaration.inductDecl _ _ _ isUnsafe => isUnsafe
| _ => false


/-- The kernel compiles (mutual) inductive declarations (see `inductiveDecls`) into a set of
    - `Declaration.inductDecl` (for each inductive datatype in the mutual Declaration),
    - `Declaration.ctorDecl` (for each Constructor in the mutual Declaration),
    - `Declaration.recDecl` (automatically generated recursors).

    This data is used to implement iota-reduction efficiently and compile nested inductive
    declarations.

    A series of checks are performed by the kernel to check whether a `inductiveDecls`
    is valid or not. -/
structure InductiveVal extends ConstantVal :=
(nparams : Nat)       -- Number of parameters
(nindices : Nat)      -- Number of indices
(all : List Name)     -- List of all (including this one) inductive datatypes in the mutual declaration containing this one
(ctors : List Name)   -- List of all constructors for this inductive datatype
(isRec : Bool)        -- `true` Iff it is recursive
(isUnsafe : Bool)
(isReflexive : Bool)

@[export lean_mk_inductive_val]
def mkInductiveValEx (name : Name) (lparams : List Name) (type : Expr) (nparams nindices : Nat)
    (all ctors : List Name) (isRec isUnsafe isReflexive : Bool) : InductiveVal :=
{ name := name, lparams := lparams, type := type, nparams := nparams, nindices := nindices, all := all, ctors := ctors,
  isRec := isRec, isUnsafe := isUnsafe, isReflexive := isReflexive }
@[export lean_inductive_val_is_rec] def InductiveVal.isRecEx (v : InductiveVal) : Bool := v.isRec
@[export lean_inductive_val_is_unsafe] def InductiveVal.isUnsafeEx (v : InductiveVal) : Bool := v.isUnsafe
@[export lean_inductive_val_is_reflexive] def InductiveVal.isReflexiveEx (v : InductiveVal) : Bool := v.isReflexive

namespace InductiveVal
def nctors (v : InductiveVal) : Nat := v.ctors.length
end InductiveVal

structure ConstructorVal extends ConstantVal :=
(induct  : Name)  -- Inductive Type this Constructor is a member of
(cidx    : Nat)   -- Constructor index (i.e., Position in the inductive declaration)
(nparams : Nat)   -- Number of parameters in inductive datatype `induct`
(nfields : Nat)   -- Number of fields (i.e., arity - nparams)
(isUnsafe : Bool)

@[export lean_mk_constructor_val]
def mkConstructorValEx (name : Name) (lparams : List Name) (type : Expr) (induct : Name) (cidx nparams nfields : Nat) (isUnsafe : Bool) : ConstructorVal :=
{ name := name, lparams := lparams, type := type, induct := induct, cidx := cidx, nparams := nparams, nfields := nfields, isUnsafe := isUnsafe }
@[export lean_constructor_val_is_unsafe] def ConstructorVal.isUnsafeEx (v : ConstructorVal) : Bool := v.isUnsafe

instance ConstructorVal.inhabited : Inhabited ConstructorVal :=
⟨{ toConstantVal := arbitrary _, induct := arbitrary _, cidx := 0, nparams := 0, nfields := 0, isUnsafe := true }⟩

/-- Information for reducing a recursor -/
structure RecursorRule :=
(ctor : Name)   -- Reduction rule for this Constructor
(nfields : Nat) -- Number of fields (i.e., without counting inductive datatype parameters)
(rhs : Expr)    -- Right hand side of the reduction rule

structure RecursorVal extends ConstantVal :=
(all : List Name)            -- List of all inductive datatypes in the mutual declaration that generated this recursor
(nparams : Nat)              -- Number of parameters
(nindices : Nat)             -- Number of indices
(nmotives : Nat)             -- Number of motives
(nminors : Nat)              -- Number of minor premises
(rules : List RecursorRule)  -- A reduction for each Constructor
(k : Bool)                   -- It supports K-like reduction
(isUnsafe : Bool)

@[export lean_mk_recursor_val]
def mkRecursorValEx (name : Name) (lparams : List Name) (type : Expr) (all : List Name) (nparams nindices nmotives nminors : Nat)
    (rules : List RecursorRule) (k isUnsafe : Bool) : RecursorVal :=
{ name := name, lparams := lparams, type := type, all := all, nparams := nparams, nindices := nindices,
  nmotives := nmotives, nminors := nminors, rules := rules, k := k, isUnsafe := isUnsafe }
@[export lean_recursor_k] def RecursorVal.kEx (v : RecursorVal) : Bool := v.k
@[export lean_recursor_is_unsafe] def RecursorVal.isUnsafeEx (v : RecursorVal) : Bool := v.isUnsafe

namespace RecursorVal
def getMajorIdx (v : RecursorVal) : Nat :=
v.nparams + v.nmotives + v.nminors + v.nindices

def getInduct (v : RecursorVal) : Name :=
v.name.getPrefix

end RecursorVal

inductive QuotKind
| type  -- `Quot`
| ctor  -- `Quot.mk`
| lift  -- `Quot.lift`
| ind   -- `Quot.ind`

structure QuotVal extends ConstantVal :=
(kind : QuotKind)

@[export lean_mk_quot_val]
def mkQuotValEx (name : Name) (lparams : List Name) (type : Expr) (kind : QuotKind) : QuotVal :=
{ name := name, lparams := lparams, type := type, kind := kind }
@[export lean_quot_val_kind] def QuotVal.kindEx (v : QuotVal) : QuotKind := v.kind

/-- Information associated with constant declarations. -/
inductive ConstantInfo
| axiomInfo    (val : AxiomVal)
| defnInfo     (val : DefinitionVal)
| thmInfo      (val : TheoremVal)
| opaqueInfo   (val : OpaqueVal)
| quotInfo     (val : QuotVal)
| inductInfo   (val : InductiveVal)
| ctorInfo     (val : ConstructorVal)
| recInfo      (val : RecursorVal)

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

def name (d : ConstantInfo) : Name :=
d.toConstantVal.name

def lparams (d : ConstantInfo) : List Name :=
d.toConstantVal.lparams

def type (d : ConstantInfo) : Expr :=
d.toConstantVal.type

def value? : ConstantInfo → Option Expr
| defnInfo {value := r, ..} => some r
| thmInfo  {value := r, ..} => some r.get
| _                         => none

def hasValue : ConstantInfo → Bool
| defnInfo {value := r, ..} => true
| thmInfo  {value := r, ..} => true
| _                         => false

def value! : ConstantInfo → Expr
| defnInfo {value := r, ..} => r
| thmInfo  {value := r, ..} => r.get
| _                         => panic! "declaration with value expected"

def hints : ConstantInfo → ReducibilityHints
| defnInfo {hints := r, ..} => r
| _                         => ReducibilityHints.opaque

def isCtor : ConstantInfo → Bool
| ctorInfo _ => true
| _          => false

@[extern "lean_instantiate_type_lparams"]
constant instantiateTypeLevelParams (c : @& ConstantInfo) (ls : @& List Level) : Expr := arbitrary _

@[extern "lean_instantiate_value_lparams"]
constant instantiateValueLevelParams (c : @& ConstantInfo) (ls : @& List Level) : Expr := arbitrary _

end ConstantInfo

def mkRecFor (declName : Name) : Name :=
mkNameStr declName "rec"

end Lean
