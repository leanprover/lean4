/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.Lean.Expr

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
Declaration during Type checking.

Remark: the ReducibilityHints are not related to the attributes: reducible/irrelevance/semireducible.
These attributes are used by the Elaborator. The ReducibilityHints are used by the kernel (and Elaborator).
Moreover, the ReducibilityHints cannot be changed after a Declaration is added to the kernel. -/
inductive ReducibilityHints
| opaque   : ReducibilityHints
| «abbrev» : ReducibilityHints
| regular  : Uint32 → ReducibilityHints

/-- Base structure for `AxiomVal`, `DefinitionVal`, `TheoremVal`, `inductiveVal`, `ConstructorVal`, `RecursorVal` and `QuotVal`. -/
structure ConstantVal :=
(id : Name) (lparams : List Name) (Type : Expr)

structure AxiomVal extends ConstantVal :=
(isUnsafe : Bool)

structure DefinitionVal extends ConstantVal :=
(value : Expr) (hints : ReducibilityHints) (isUnsafe : Bool)

structure TheoremVal extends ConstantVal :=
(value : Task Expr)

/- Value for an opaque constant Declaration `constant x : t := e` -/
structure OpaqueVal extends ConstantVal :=
(value : Expr)

structure Constructor :=
(id : Name) (Type : Expr)

structure inductiveType :=
(id : Name) (Type : Expr) (cnstrs : List Constructor)

/-- Declaration object that can be sent to the kernel. -/
inductive Declaration
| axiomDecl       (val : AxiomVal)
| defnDecl        (val : DefinitionVal)
| thmDecl         (val : TheoremVal)
| opaqueDecl      (val : OpaqueVal)
| quotDecl
| mutualDefnDecl (defns : List DefinitionVal) -- All definitions must be marked as `unsafe`
| inductDecl      (lparams : List Name) (nparams : Nat) (types : List inductiveType) (isUnsafe : Bool)

/-- The kernel compiles (mutual) inductive declarations (see `inductiveDecls`) into a set of
    - `Declaration.inductDecl` (for each inductive datatype in the mutual Declaration),
    - `Declaration.cnstrDecl` (for each Constructor in the mutual Declaration),
    - `Declaration.recDecl` (automatically generated recursors).

    This data is used to implement iota-reduction efficiently and compile nested inductive
    declarations.

    A series of checks are performed by the kernel to check whether a `inductiveDecls`
    is valid or not. -/
structure inductiveVal extends ConstantVal :=
(nparams : Nat)       -- Number of parameters
(nindices : Nat)      -- Number of indices
(all : List Name)     -- List of all (including this one) inductive datatypes in the mutual Declaration containing this one
(cnstrs : List Name)  -- List of all constructors for this inductive datatype
(isRec : Bool)       -- `tt` Iff it is recursive
(isUnsafe : Bool)
(isReflexive : Bool)

structure ConstructorVal extends ConstantVal :=
(induct  : Name)  -- Inductive Type this Constructor is a member of
(cidx    : Nat)   -- Constructor index (i.e., Position in the inductive Declaration)
(nparams : Nat)   -- Number of parameters in inductive datatype `induct`
(nfields : Nat)   -- Number of fields (i.e., arity - nparams)
(isUnsafe : Bool)

/-- Information for reducing a recursor -/
structure RecursorRule :=
(cnstr : Name)  -- Reduction rule for this Constructor
(nfields : Nat) -- Number of fields (i.e., without counting inductive datatype parameters)
(rhs : Expr)    -- Right hand side of the reduction rule

structure RecursorVal extends ConstantVal :=
(all : List Name)            -- List of all inductive datatypes in the mutual Declaration that generated this recursor
(nparams : Nat)              -- Number of parameters
(nindices : Nat)             -- Number of indices
(nmotives : Nat)             -- Number of motives
(nminor : Nat)               -- Number of minor premises
(rules : List RecursorRule) -- A reduction for each Constructor
(k : Bool)                   -- It supports K-like reduction
(isUnsafe : Bool)

inductive QuotKind
| Type  -- `Quot`
| cnstr -- `Quot.mk`
| lift  -- `Quot.lift`
| ind   -- `Quot.ind`

structure QuotVal extends ConstantVal :=
(kind : QuotKind)

/-- Information associated with constant declarations. -/
inductive ConstantInfo
| axiomInfo    (val : AxiomVal)
| defnInfo     (val : DefinitionVal)
| thmInfo      (val : TheoremVal)
| opaqueInfo   (val : OpaqueVal)
| quotInfo     (val : QuotVal)
| inductInfo   (val : inductiveVal)
| cnstrInfo    (val : ConstructorVal)
| recInfo      (val : RecursorVal)

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
| (defnInfo     {toConstantVal := d, ..}) := d
| (axiomInfo    {toConstantVal := d, ..}) := d
| (thmInfo      {toConstantVal := d, ..}) := d
| (opaqueInfo   {toConstantVal := d, ..}) := d
| (quotInfo     {toConstantVal := d, ..}) := d
| (inductInfo   {toConstantVal := d, ..}) := d
| (cnstrInfo    {toConstantVal := d, ..}) := d
| (recInfo      {toConstantVal := d, ..}) := d

def id (d : ConstantInfo) : Name :=
d.toConstantVal.id

def lparams (d : ConstantInfo) : List Name :=
d.toConstantVal.lparams

def Type (d : ConstantInfo) : Expr :=
d.toConstantVal.Type

def value : ConstantInfo → Option Expr
| (defnInfo {value := r, ..}) := some r
| (thmInfo  {value := r, ..}) := some r.get
| _                            := none

def hints : ConstantInfo → ReducibilityHints
| (defnInfo {hints := r, ..}) := r
| _                            := ReducibilityHints.opaque

end ConstantInfo
end Lean
