/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr

namespace lean
/--
Reducibility hints are used in the convertibility checker.
When trying to solve a constraint such a

           (f ...) =?= (g ...)

where f and g are definitions, the checker has to decide which one will be unfolded.
  If      f (g) is opaque,     then g (f) is unfolded if it is also not marked as opaque,
  Else if f (g) is abbrev,     then f (g) is unfolded if g (f) is also not marked as abbrev,
  Else if f and g are regular, then we unfold the one with the biggest definitional height.
  Otherwise both are unfolded.

The arguments of the `regular` constructor are: the definitional height and the flag `selfOpt`.

The definitional height is by default computed by the kernel. It only takes into account
other regular definitions used in a definition. When creating declarations using meta-programming,
we can specify the definitional depth manually.

Remark: the hint only affects performance. None of the hints prevent the kernel from unfolding a
declaration during type checking.

Remark: the reducibilityHints are not related to the attributes: reducible/irrelevance/semireducible.
These attributes are used by the elaborator. The reducibilityHints are used by the kernel (and elaborator).
Moreover, the reducibilityHints cannot be changed after a declaration is added to the kernel. -/
inductive reducibilityHints
| opaque   : reducibilityHints
| «abbrev» : reducibilityHints
| regular  : uint32 → reducibilityHints

/-- Base structure for `axiomVal`, `definitionVal`, `theoremVal`, `inductiveVal`, `constructorVal`, `recursorVal` and `quotVal`. -/
structure constantVal :=
(id : name) (lparams : list name) (type : expr)

structure axiomVal extends constantVal :=
(isUnsafe : bool)

structure definitionVal extends constantVal :=
(value : expr) (hints : reducibilityHints) (isUnsafe : bool)

structure theoremVal extends constantVal :=
(value : task expr)

/- Value for an opaque constant declaration `constant x : t := e` -/
structure opaqueVal extends constantVal :=
(value : expr)

structure constructor :=
(id : name) (type : expr)

structure inductiveType :=
(id : name) (type : expr) (cnstrs : list constructor)

/-- Declaration object that can be sent to the kernel. -/
inductive declaration
| axiomDecl       (val : axiomVal)
| defnDecl        (val : definitionVal)
| thmDecl         (val : theoremVal)
| opaqueDecl      (val : opaqueVal)
| quotDecl
| mutualDefnDecl (defns : list definitionVal) -- All definitions must be marked as `unsafe`
| inductDecl      (lparams : list name) (nparams : nat) (types : list inductiveType) (isUnsafe : bool)

/-- The kernel compiles (mutual) inductive declarations (see `inductiveDecls`) into a set of
    - `declaration.inductDecl` (for each inductive datatype in the mutual declaration),
    - `declaration.cnstrDecl` (for each constructor in the mutual declaration),
    - `declaration.recDecl` (automatically generated recursors).

    This data is used to implement iota-reduction efficiently and compile nested inductive
    declarations.

    A series of checks are performed by the kernel to check whether a `inductiveDecls`
    is valid or not. -/
structure inductiveVal extends constantVal :=
(nparams : nat)       -- Number of parameters
(nindices : nat)      -- Number of indices
(all : list name)     -- List of all (including this one) inductive datatypes in the mutual declaration containing this one
(cnstrs : list name)  -- List of all constructors for this inductive datatype
(isRec : bool)       -- `tt` iff it is recursive
(isUnsafe : bool)
(isReflexive : bool)

structure constructorVal extends constantVal :=
(induct  : name)  -- Inductive type this constructor is a member of
(cidx    : nat)   -- Constructor index (i.e., position in the inductive declaration)
(nparams : nat)   -- Number of parameters in inductive datatype `induct`
(nfields : nat)   -- Number of fields (i.e., arity - nparams)
(isUnsafe : bool)

/-- Information for reducing a recursor -/
structure recursorRule :=
(cnstr : name)  -- Reduction rule for this constructor
(nfields : nat) -- Number of fields (i.e., without counting inductive datatype parameters)
(rhs : expr)    -- Right hand side of the reduction rule

structure recursorVal extends constantVal :=
(all : list name)            -- List of all inductive datatypes in the mutual declaration that generated this recursor
(nparams : nat)              -- Number of parameters
(nindices : nat)             -- Number of indices
(nmotives : nat)             -- Number of motives
(nminor : nat)               -- Number of minor premises
(rules : list recursorRule) -- A reduction for each constructor
(k : bool)                   -- It supports K-like reduction
(isUnsafe : bool)

inductive quotKind
| type  -- `quot`
| cnstr -- `quot.mk`
| lift  -- `quot.lift`
| ind   -- `quot.ind`

structure quotVal extends constantVal :=
(kind : quotKind)

/-- Information associated with constant declarations. -/
inductive constantInfo
| axiomInfo    (val : axiomVal)
| defnInfo     (val : definitionVal)
| thmInfo      (val : theoremVal)
| opaqueInfo   (val : opaqueVal)
| quotInfo     (val : quotVal)
| inductInfo   (val : inductiveVal)
| cnstrInfo    (val : constructorVal)
| recInfo      (val : recursorVal)

namespace constantInfo

def toConstantVal : constantInfo → constantVal
| (defnInfo     {toConstantVal := d, ..}) := d
| (axiomInfo    {toConstantVal := d, ..}) := d
| (thmInfo      {toConstantVal := d, ..}) := d
| (opaqueInfo   {toConstantVal := d, ..}) := d
| (quotInfo     {toConstantVal := d, ..}) := d
| (inductInfo   {toConstantVal := d, ..}) := d
| (cnstrInfo    {toConstantVal := d, ..}) := d
| (recInfo      {toConstantVal := d, ..}) := d

def id (d : constantInfo) : name :=
d.toConstantVal.id

def lparams (d : constantInfo) : list name :=
d.toConstantVal.lparams

def type (d : constantInfo) : expr :=
d.toConstantVal.type

def value : constantInfo → option expr
| (defnInfo {value := r, ..}) := some r
| (thmInfo  {value := r, ..}) := some r.get
| _                            := none

def hints : constantInfo → reducibilityHints
| (defnInfo {hints := r, ..}) := r
| _                            := reducibilityHints.opaque

end constantInfo
end lean
