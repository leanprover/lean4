/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.StateC

/-!
# InLean: the environment, read at use

Twin of `ConLeche/Kernel/FEnv.lean` over `Lean.Kernel.Environment`.  What
con-leche's install computes from a declaration group and stores beside
the constants (`ConLeche/Kernel/Install.lean`: `IndCaps`, a recursor's
counts and the firing mode of its rules, the projection tables) is read
here off Lean's own entry, when a check asks for it.  Nothing is stored
and nothing is memoised:

* **`IndCaps`** (`indView?`, twin of `blockCapsAt`): every field is a field
  of the `InductiveVal` (`all`, `numParams`, `numIndices`, `ctors`, and
  official's `is_rec` as `isRec`, which is con-leche's `blockIsRec`) or of
  its one constructor's `ConstructorVal` (`numFields`).  One lookup and a
  small record per use.
* **A recursor's counts** (`recView?`): `majorIdx` and `rulePrefix` are sums
  of the `RecursorVal`'s counts, its K flag is `k`, its rules are `rules`.
  **The firing mode** (`recFireAt`, twin of `recFire`) is computed only
  where a check reads it (ι's case-3 certificate): `.plain` when the major
  premise's domain is headed by a member of the block, else `.nested` at
  that domain's levels and parameters.
* **A constructor's counts** (`ctorView?`): `numParams`, `numFields`.
* **Projection tables** (`findProj?`, twin of `blockTables` read at a
  field): a table exists for an index-free one-constructor inductive whose
  constructor type binds its parameters and fields; that is a binder count,
  with no substitution, since substituting never makes or removes a
  binder.  The entry carries no body: only inference reads one, and builds
  just that field's (`projBodyAt`).
* **The quotient package** (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`):
  con-leche stores its pins at the record's level names (`quotAt`); here
  Lean's own types, which the quotient's check compares with the pins, and
  the pins' rules (`quotRuleRhs`, `Lean/Kernel/InLean/Pins.lean`'s twins).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## The environment -/

/-- Twin of `FEnv`: the environment a check reads, and the declaration's
safety (official `m_definition_safety`; con-leche checks safe declarations
only). -/
structure FEnv where
  env : Kernel.Environment
  safety : DefinitionSafety := .safe
  /-- **The axiom policy.**  `false`, con-leche's: `sorryAx` is not a
  constant (con-leche installs nothing for it, `declConstants`), so any use
  declines.  `true`, the official kernel's, what Lean needs for ordinary
  use: `sorryAx` is the constant Lean stores, and a certified `Nat`
  operation's name may hold any declaration. -/
  coreAxioms : Bool := false

/-- Twin of `FEnv.find?`. -/
@[inline] def FEnv.find? (fe : FEnv) (n : Name) : Option ConstantInfo :=
  if n == sorryAxName && !fe.coreAxioms then none else fe.env.find? n

/-! ## Inductives -/

/-- Twin of `IndCaps`. -/
structure IndCaps where
  eta : Bool := false
  etaCtor : Name := .anonymous
  etaParams : Nat := 0
  etaFields : Nat := 0
  unitlike : Bool := false
  unitParams : Nat := 0
  all : List Name := []
  nparams : Nat := 0
  nIdx : Nat := 0
  ctors : List Name := []
  deriving Inhabited

/-- **Twin of `blockCapsAt`**, read off the `InductiveVal` and its one
constructor. -/
def capsOf (env : Kernel.Environment) (v : InductiveVal) : IndCaps :=
  match v.ctors with
  | [c] =>
    let nF := match env.find? c with
      | some (.ctorInfo cv) => cv.numFields
      | _ => 0
    { eta := v.numIndices == 0 && !v.isRec
      etaCtor := c
      etaParams := v.numParams
      etaFields := nF
      unitlike := v.numIndices == 0 && nF == 0 && !v.isRec
      unitParams := v.numParams
      all := v.all
      nparams := v.numParams
      nIdx := v.numIndices
      ctors := [c] }
  | cs => { all := v.all, nparams := v.numParams, nIdx := v.numIndices, ctors := cs }

/-- **The twin of a lookup finding `.indInfo cvT caps`**: an inductive type
former and its capabilities, or `Quot` (the pin's empty capabilities). -/
def FEnv.indView? (fe : FEnv) (n : Name) : Option (ConstantVal × IndCaps) :=
  match fe.find? n with
  | some (.inductInfo v) => some (v.toConstantVal, capsOf fe.env v)
  | some (.quotInfo q) => if q.kind == .type then some (q.toConstantVal, {}) else none
  | _ => none

/-- **The twin of a lookup finding `.ctorInfo cv nP nF`**: a constructor
and its counts, or `Quot.mk` (two parameters, one field). -/
def FEnv.ctorView? (fe : FEnv) (n : Name) : Option (ConstantVal × Nat × Nat) :=
  match fe.find? n with
  | some (.ctorInfo v) => some (v.toConstantVal, v.numParams, v.numFields)
  | some (.quotInfo q) => if q.kind == .ctor then some (q.toConstantVal, 2, 1) else none
  | _ => none

/-- Twin of `isCtorAppC`. -/
def isCtorAppC (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const cn _ => (fe.ctorView? cn).isSome
  | _ => false

/-- Twin of `etaCtorShapeC`. -/
def etaCtorShapeC (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
    match fe.ctorView? c with
    | some (_, cnP, cnF) => e.getAppNumArgs == cnP + cnF
    | none => false
  | _ => false

/-! ## Definitions -/

/-- Twin of a lookup finding `.defnInfo cv v hint`. -/
@[inline] def FEnv.defnView? (fe : FEnv) (n : Name) :
    Option (ConstantVal × Expr × ReducibilityHints) :=
  match fe.find? n with
  | some (.defnInfo v) => some (v.toConstantVal, v.value, v.hints)
  | _ => none

/-- Twin of `headHintC`.  con-leche's hints are `opaque`/`abbrev`/`regular
h`, Lean's the same. -/
def headHintC (fe : FEnv) (e : Expr) : ReducibilityHints :=
  match e.getAppFn with
  | .const nm _ =>
    match fe.defnView? nm with
    | some (_, _, hint) => hint
    | none => .opaque
  | _ => .opaque

/-- Twin of `unfoldableHeadC`. -/
def unfoldableHeadC (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const nm us =>
    match fe.defnView? nm with
    | some (cv, _, _) => us.length == cv.levelParams.length
    | none => false
  | _ => false

/-- Twin of `ReducibilityHint.lt`. -/
def hintLt : ReducibilityHints → ReducibilityHints → Bool
  | _, .opaque => false
  | .abbrev, _ => false
  | .opaque, _ => true
  | _, .abbrev => true
  | .regular h₁, .regular h₂ => h₁ < h₂

/-- Twin of `ReducibilityHint.sameRegular`. -/
def hintSameRegular : ReducibilityHints → ReducibilityHints → Bool
  | .regular h₁, .regular h₂ => h₁ == h₂
  | _, _ => false

/-! ## Recursors -/

/-- Twin of `RecRuleFire`. -/
inductive RecRuleFire where
  | plain
  | nested (lvls : List Level) (pins : List Expr)
  | levels (lvls : List Level)

/-- The quotient package's eliminators as recursors (the pins `quotLiftA`,
`quotIndA`): `majorIdx = rulePrefix = 5` (resp. 4), no K, one rule on
`Quot.mk` with one field, firing at the eliminator's first level. -/
def quotRecVal (q : QuotVal) (rhs : Expr) : Option RecursorVal :=
  let n := if q.kind == .lift then 5 else 4
  if q.kind == .lift || q.kind == .ind then
    some { name := q.name, levelParams := q.levelParams, type := q.type, all := [quotName],
           numParams := n, numIndices := 0, numMotives := 0, numMinors := 0,
           rules := [{ ctor := quotMkName, nfields := 1, rhs }], k := false, isUnsafe := false }
  else none

/-- **The twin of a lookup finding `.recInfo cv mI rP isK rules`**: a
recursor (its counts are sums of the `RecursorVal`'s), or a quotient
eliminator (`quotRecVal`, its rule's right-hand side at the record's level
names supplied by `quotRhs`). -/
def FEnv.recView? (fe : FEnv) (quotRhs : QuotVal → Expr) (n : Name) : Option RecursorVal :=
  match fe.find? n with
  | some (.recInfo rv) => some rv
  | some (.quotInfo q) => quotRecVal q (quotRhs q)
  | _ => none

/-- `majorIdx`: the major premise's argument position. -/
@[inline] def majorIdxOf (rv : RecursorVal) : Nat :=
  rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices

/-- `rulePrefix`: the argument prefix a rule's right-hand side takes. -/
@[inline] def rulePrefixOf (rv : RecursorVal) : Nat :=
  rv.numParams + rv.numMotives + rv.numMinors

/-- The type under `n` binders. -/
def piBody? : Nat → Expr → Option Expr
  | 0, e => some e
  | n + 1, .forallE _ _ b _ => piBody? n b
  | _, _ => none

/-- Twin of `Expr.dropVars`: `n` variables below a term's own, which do not
occur in it, dropped. -/
def dropVars : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => dropVars n (e.inst1I (.sort .zero))

/-- **Twin of `recFire`**, at use: `.plain` at a member major; at a major
outside the block, `.nested` at the levels and parameters of its
container, the parameters moved from under the index binders to the rule
prefix; the quotient eliminators fire at their first level (`.levels`). -/
def recFireAt (rv : RecursorVal) (isQuot : Bool) : RecRuleFire :=
  if isQuot then .levels [.param (rv.levelParams.headD .anonymous)] else
  match piBody? (majorIdxOf rv) rv.type with
  | some (.forallE _ dom _ _) =>
    match dom.getAppFn with
    | .const T us =>
      if rv.all.contains T then .plain
      else
        let nI := majorIdxOf rv - rulePrefixOf rv
        let args := dom.getAppArgs.toList
        .nested us ((args.take (args.length - nI)).map (dropVars nI))
    | _ => .plain
  | _ => .plain

/-- Twin of the `.recInfo` arity read of `iotaArityOk`. -/
def FEnv.recArity? (fe : FEnv) (n : Name) : Option (Nat × Nat) :=
  match fe.find? n with
  | some (.recInfo rv) => some (majorIdxOf rv, rv.levelParams.length)
  | some (.quotInfo q) =>
    match q.kind with
    | .lift => some (5, q.levelParams.length)
    | .ind => some (4, q.levelParams.length)
    | _ => none
  | _ => none

/-! ## Projection tables -/

/-- Twin of `ProjEntry`, without the body (`projBodyAt` builds it where
inference needs it). -/
structure ProjEntry where
  structName : Name
  idx : Nat
  levelParams : List Name
  numParams : Nat
  ctor : Name
  numFields : Nat
  /-- the constructor's type, which the body is read off -/
  ctorType : Expr

/-- Does `e` bind at least `n` syntactic `∀`s? -/
def hasPis : Nat → Expr → Bool
  | 0, _ => true
  | n + 1, .forallE _ _ b _ => hasPis n b
  | _, _ => false

/-- **Twin of `FEnv.findProj?`**: the table of `T` exists exactly where
con-leche's install stores one (`blockTables`: one constructor, no index,
`structProjBodies` succeeds, i.e. the constructor's type binds the
parameters and the fields), and field `i` is below the field count. -/
def FEnv.findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry :=
  match fe.find? T with
  | some (.inductInfo v) =>
    match v.ctors with
    | [c] =>
      if v.numIndices == 0 then
        match fe.find? c with
        | some (.ctorInfo cv) =>
          if i < cv.numFields && hasPis (v.numParams + cv.numFields) cv.type then
            some ⟨T, i, v.levelParams, v.numParams, c, cv.numFields, cv.type⟩
          else none
        | _ => none
      else none
    | _ => none
  | _ => none

/-- Does `T` have a table (twin of `(fe.findTable? T).isSome`)? -/
def FEnv.hasTable (fe : FEnv) (T : Name) : Bool :=
  match fe.find? T with
  | some (.inductInfo v) =>
    match v.ctors with
    | [c] =>
      v.numIndices == 0 &&
        match fe.find? c with
        | some (.ctorInfo cv) => hasPis (v.numParams + cv.numFields) cv.type
        | _ => false
    | _ => false
  | _ => false

/-- **Twin of `structProjBodies`' field `i`**: the constructor type's
parameters replaced by `bvar (nP - k)`, the fields before `i` by the
subject's projections `.proj T j (bvar 0)`, and field `i`'s domain read
off. -/
def projBodyAt (T : Name) (nP i : Nat) (cty : Expr) : Option Expr :=
  let rec params : Nat → Expr → Option Expr
    | k, e =>
      if k < nP then
        match e with
        | .forallE _ _ b _ => params (k + 1) (b.inst1I (.bvar (nP - k)))
        | _ => none
      else some e
    termination_by k => nP - k
  let rec fields : Nat → Expr → Option Expr
    | j, .forallE _ d b _ =>
      if j < i then fields (j + 1) (b.inst1I (.proj T j (.bvar 0))) else some d
    | _, _ => none
    termination_by j => i - j
  (params 0 cty).bind (fields 0)

/-- Twin of `structProjBodies`: every field's body (the block check's
`checkBlockTablesF` reads them all). -/
def structProjBodies (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  if hasPis (nP + nF) cty then
    (List.range nF).toArray.mapM fun i => projBodyAt T nP i cty
  else none

/-- Twin of `ProjEntry.typeAtI`: the body at the levels, the subject type's
arguments and the subject. -/
def ProjEntry.typeAtI (entry : ProjEntry) (us : List Level) (targs : List Expr) (pe : Expr) :
    Option Expr :=
  (projBodyAt entry.structName entry.numParams entry.idx entry.ctorType).map fun body =>
    (body.instLvlParamsI entry.levelParams us).instI (#[pe] ++ targs.toArray.reverse)

/-- The field count of `T`'s table, where it has one. -/
def FEnv.tableFields? (fe : FEnv) (T : Name) : Option Nat :=
  match fe.find? T with
  | some (.inductInfo v) =>
    match v.ctors with
    | [c] =>
      if v.numIndices == 0 then
        match fe.find? c with
        | some (.ctorInfo cv) =>
          if hasPis (v.numParams + cv.numFields) cv.type then some cv.numFields else none
        | _ => none
      else none
    | _ => none
  | _ => none

/-- Twin of `FEnv.towerSlotsAllF` (`∀ j < nF, findProj? T j` holds): no slot
to ask for, or a table with at least `nF` fields — one lookup and one binder
count, not one per field. -/
def FEnv.towerSlotsAllF (fe : FEnv) (T : Name) (nF : Nat) : Bool :=
  nF == 0 || match fe.tableFields? T with
    | some n => nF ≤ n
    | none => false

/-- Twin of `FEnv.andRescueSlotsF` (`andRescueSlotsOf`). -/
def FEnv.andRescueSlotsF (fe : FEnv) (ctor : Name) (nP : Nat) : Bool :=
  (List.range 2).all fun j =>
    match fe.findProj? andName j with
    | some e => e.ctor == ctor && e.numParams == nP && e.numFields == 2
    | none => false

/-! ## Literal support -/

/-- Twin of `natLitStoredF`. -/
def natLitStoredF (fe : FEnv) : Bool :=
  (fe.find? natName).isSome && (fe.find? natZeroName).isSome && (fe.find? natSuccName).isSome

/-- Twin of `strLitStoredF`. -/
def strLitStoredF (fe : FEnv) : Bool :=
  natLitStoredF fe && (fe.find? stringName).isSome && (fe.find? stringOfListName).isSome &&
    (fe.find? listName).isSome && (fe.find? listNilName).isSome &&
    (fe.find? listConsName).isSome && (fe.find? charName).isSome &&
    (fe.find? charOfNatName).isSome

end Lean.Kernel.InLean
