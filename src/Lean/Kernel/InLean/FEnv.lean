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

Twin of `ConLeche.Kernel.FEnv` over `Lean.Kernel.Environment`.  What
con-leche's install computes from a declaration group and stores beside
the constants (`ConLeche.Kernel.Install`: `IndCaps`, a recursor's
counts and the firing mode of its rules, the projection tables) is read
here off Lean's own entry, when a check asks for it.  Nothing is stored
and nothing is memoised:

* **`IndCaps`** (`indView?`, twin of `blockCapsAt`): every field is a field
  of the `InductiveVal` (`all`, `numParams`, `numIndices`, `ctors`, and
  official's `is_rec` as `isRec`, which is con-leche's `blockIsRec`) or of
  its one constructor's `ConstructorVal` (`numFields`), but the family's sort
  fact `neverZero`, which is read off the former's type as the
  install reads its declared one (`formerZ`: the `∀`-telescope to its sort,
  a walk of the parameters and indices).  One lookup and a small record per
  use.
* **A recursor's counts** (`recView?`): `majorIdx` and `rulePrefix` are sums
  of the `RecursorVal`'s counts, its K flag is `k`, its rules are `rules`.
  **The firing mode** (`recFireAt`, twin of `recFire`) is computed only
  where a check reads it (ι's case-3 certificate): `.plain` when the major
  premise's domain is headed by a member of the block, else `.nested` at
  that domain's levels and parameters.
* **A constructor's counts and family** (`ctorView?`): `numParams`, `numFields`,
  `induct` (the family con-leche's install stores on the record).
* **Projection tables** (`findProj?`, twin of `blockTables` read at a
  field): a table exists for an index-free one-constructor inductive whose
  constructor type binds its parameters and fields; that is a binder count,
  with no substitution, since substituting never makes or removes a
  binder.  The entry carries no body: only inference reads one, and builds
  just that field's (`projBodyAt`).
* **What a check sees** (`FEnv.sees`): not `sorryAx`
  at con-leche's axiom policy, and in the check of a safe declaration no
  `unsafe` or `partial` constant.  Freshness is read off Lean's environment
  itself, as official's `check_name`.
* **The block being checked** (`FEnv.pending`): inside an inductive block's
  job, a member reads as master's staged environments hold it (no
  projection table).
* **The quotient package** (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`):
  con-leche stores its pins at the record's level names (`quotAt`); here
  Lean's own types, which the quotient's check compares with the pins, and
  the pins' rules (`quotRuleRhs`, `Lean.Kernel.InLean.Pins`'s twins).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## The environment -/

/-- **What the core reports to the limits' poll** (`Limits.poll`): a body
it is about to run, at its depth (official `check_system`'s sites), and a
constant it unfolds: a definition's δ, a recursor's or the quotient's ι
(official `record_unfold`, the diagnostics' counter). -/
inductive Event where
  | body (depth : Nat)
  | unfold (n : Name)

/-- **The official kernel's resource limits** (con-leche has none; the
defaults impose none but the numerals' size).  Each only adds an error
exit, so the checker's soundness holds whatever they are.

* `recDepth`: the core's entry points nest at most this deep (the knot's
  fuel; `none` is `checkFuel`), official `scope_rec_depth`'s bound.
* `poll`: if any, asked at every body the knot's memos miss (for
  `whnfCore`, whose memo is read inside its loop, at every entry that is not
  an easy case) and at every unfolding (`Event`); a limit it answers is the
  error.  The heartbeat
  budget, the cancellation token and the diagnostics' unfold counter live
  behind it (core's glue reads and writes the runtime).
* `maxNatSize`: twin of con-leche's `maxNatSize` (the run's parameter,
  `CState.maxNatSize`): the largest numeral the core computes or infers, in
  bytes (`natSizeBytes`), official `LEAN_NAT_MAX_SIZE` (default 128 MiB,
  `maxNatSizeDefault`). -/
structure Limits where
  recDepth : Option Nat := none
  poll : Option (Event → Option Limit) := none
  maxNatSize : Nat := 134217728

instance : Inhabited Limits := ⟨{}⟩

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
  operation's name may hold an axiom (`checkAxiomC`). -/
  coreAxioms : Bool := false
  /-- **The inductive block being checked** (empty outside its job): its
  members' names.  Master's job runs its stages at environments built from
  the shape (`consBlockIndsF` pushes each former at `blockCapsAt`; no
  projection table exists until the block's install); InLean's at-use
  readers read a marked member as those environments do: no projection
  table (`findTable?` and its readers).  Set where the formers are pushed
  (`checkBlockIndsC`); the job's environments are dropped with it, so the
  installed block is read off its entries. -/
  pending : List Name := []
  /-- The resource limits (`Limits`). -/
  limits : Limits := {}

/-- Is a constant safe (neither `unsafe` nor `partial`)? -/
def safeConst : ConstantInfo → Bool
  | .defnInfo v => match v.safety with
    | .safe => true
    | _ => false
  | ci => !ci.isUnsafe

/-- **Does a check at `fe` see the constant `ci` stored at `n`?**  Not
`sorryAx` unless `coreAxioms` (con-leche installs nothing for it); in the
check of a safe declaration, no `unsafe` or `partial` constant (con-leche
checks no such declaration, and official rejects a safe declaration using
one: only the message differs, "unknown constant"). -/
@[inline] def FEnv.sees (fe : FEnv) (n : Name) (ci : ConstantInfo) : Bool :=
  !(n == sorryAxName && !fe.coreAxioms) &&
    match fe.safety with
    | .safe => safeConst ci
    | _ => true

/-- Twin of `FEnv.find?`: the constants the check sees (`FEnv.sees`).  A
name's freshness is read off the environment itself (`fe.env.find?`), as
official's. -/
@[inline] def FEnv.find? (fe : FEnv) (n : Name) : Option ConstantInfo :=
  match fe.env.find? n with
  | some ci => if fe.sees n ci then some ci else none
  | none => none

/-- Is `T` a member of the block being checked (`FEnv.pending`)? -/
@[inline] def FEnv.isPending (fe : FEnv) (T : Name) : Bool :=
  fe.pending.contains T

/-! ## Inductives -/

/-- Twin of `Expr.piResult`. -/
def piResult : Expr → Expr
  | .mdata _ e => piResult e
  | .forallE _ _ b _ => piResult b
  | e => e

/-- Twin of `formerResSort`. -/
def formerResSort (ty : Expr) : Option Level :=
  match EO.stripTop (piResult ty) with
  | .sort s => some s
  | _ => none

/-- Twin of `formerZ`. -/
def formerZ (cvT : ConstantVal) : PropWhen :=
  match formerResSort cvT.type with
  | some s => Lvl.zeronessOf s
  | none => .ifAllZero []

/-- Twin of `IndCaps`. -/
structure IndCaps where
  eta : Bool := false
  all : List Name := []
  nparams : Nat := 0
  nIdx : Nat := 0
  ctors : List Name := []
  neverZero : Bool := false
  deriving Inhabited

/-- **Twin of `blockCapsAt`**, read off the `InductiveVal`.  The family's
sort fact (`neverZero`) is the former's type read as the install
reads its declared one (`formerZ`): its `∀`-telescope walked to the sort. -/
def capsOf (v : InductiveVal) : IndCaps :=
  match v.ctors with
  | [c] =>
    { eta := v.numIndices == 0 && !v.isRec
      all := v.all
      nparams := v.numParams
      nIdx := v.numIndices
      ctors := [c]
      neverZero := (formerZ v.toConstantVal).isNever }
  | cs => { all := v.all, nparams := v.numParams, nIdx := v.numIndices, ctors := cs,
            neverZero := (formerZ v.toConstantVal).isNever }

/-- **The twin of a lookup finding `.indInfo cvT caps`**: an inductive type
former and its capabilities, or `Quot` (the pin's empty capabilities). -/
def FEnv.indView? (fe : FEnv) (n : Name) : Option (ConstantVal × IndCaps) :=
  match fe.find? n with
  | some (.inductInfo v) => some (v.toConstantVal, capsOf v)
  | some (.quotInfo q) => if q.kind == .type then some (q.toConstantVal, {}) else none
  | _ => none

/-- **The twin of a lookup finding `.ctorInfo cv nP nF induct`**: a
constructor, its counts and its family (Lean's `ConstructorVal.induct`), or
`Quot.mk` (two parameters, one field, the family `Quot`). -/
def FEnv.ctorView? (fe : FEnv) (n : Name) : Option (ConstantVal × Nat × Nat × Name) :=
  match fe.find? n with
  | some (.ctorInfo v) => some (v.toConstantVal, v.numParams, v.numFields, v.induct)
  | some (.quotInfo q) => if q.kind == .ctor then some (q.toConstantVal, 2, 1, quotName) else none
  | _ => none

/-- Twin of `isCtorAppC`. -/
def isCtorAppC (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFnT with
  | .const cn _ => (fe.ctorView? cn).isSome
  | _ => false

/-- Twin of `etaCtorShapeC`. -/
def etaCtorShapeC (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFnT with
  | .const c _ =>
    match fe.ctorView? c with
    | some (_, cnP, cnF, _) => e.getAppNumArgsT == cnP + cnF
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
  match e.getAppFnT with
  | .const nm _ =>
    match fe.defnView? nm with
    | some (_, _, hint) => hint
    | none => .opaque
  | _ => .opaque

/-- Twin of `unfoldableHeadC`. -/
def unfoldableHeadC (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFnT with
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
  | n + 1, .mdata _ e => piBody? (n + 1) e
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
  match (piBody? (majorIdxOf rv) rv.type).map EO.stripTop with
  | some (.forallE _ dom _ _) =>
    match dom.getAppFnT with
    | .const T us =>
      if rv.all.contains T then .plain
      else
        let nI := majorIdxOf rv - rulePrefixOf rv
        let args := dom.getAppArgsT.toList
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
  | n + 1, .mdata _ e => hasPis (n + 1) e
  | _, _ => false

/-- **A projection table as the checker reads it** (`FEnv.findTable?`, the
twin of a stored `ProjTable`, the block check's twin of which is
`Lean.Kernel.InLean.ProjTable`), without the bodies (`projBodyAt` builds field `i`'s
where inference needs it): the structure, its former's level parameters
and parameter count, its one constructor and that constructor's field
count and type. -/
structure TableView where
  structName : Name
  levelParams : List Name
  numParams : Nat
  ctor : Name
  numFields : Nat
  /-- the constructor's type, which the bodies are read off -/
  ctorType : Expr

/-- Twin of `ProjTable.entry`: the table viewed at field `i`. -/
@[inline] def TableView.entry (tbl : TableView) (i : Nat) : ProjEntry :=
  ⟨tbl.structName, i, tbl.levelParams, tbl.numParams, tbl.ctor, tbl.numFields, tbl.ctorType⟩

/-- **Twin of `FEnv.findTable?`**: the table of `T` exists exactly where
con-leche's install stores one (`blockTables`: one constructor, no index,
`structProjBodies` succeeds, i.e. the constructor's type binds the
parameters and the fields), at any field count; a member of the block being
checked has none (`FEnv.pending`: master's job installs no table before the
block's install). -/
def FEnv.findTable? (fe : FEnv) (T : Name) : Option TableView :=
  match fe.find? T with
  | some (.inductInfo v) =>
    if fe.isPending v.name then none else
    match v.ctors with
    | [c] =>
      if v.numIndices == 0 then
        match fe.find? c with
        | some (.ctorInfo cv) =>
          if hasPis (v.numParams + cv.numFields) cv.type then
            some ⟨T, v.levelParams, v.numParams, c, cv.numFields, cv.type⟩
          else none
        | _ => none
      else none
    | _ => none
  | _ => none

/-- **Twin of `FEnv.findProj?`**: `T`'s table, viewed at field `i` (`none`
beyond the table's field count). -/
def FEnv.findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry :=
  match fe.findTable? T with
  | some tbl => if i < tbl.numFields then some (tbl.entry i) else none
  | none => none

/-- Does `T` have a table (twin of `(fe.findTable? T).isSome`)? -/
def FEnv.hasTable (fe : FEnv) (T : Name) : Bool :=
  (fe.findTable? T).isSome

/-- Twin of `Expr.peelPis`. -/
def peelPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ _ b _ => peelPis k b
  | k + 1, .mdata _ e => peelPis (k + 1) e
  | _ + 1, _ => none

/-- Twin of `Expr.binderDom`. -/
def binderDom : Nat → Expr → Option Expr
  | k, .mdata _ e => binderDom k e
  | 0, .forallE _ A _ _ => some A
  | k + 1, .forallE _ _ b _ => binderDom k b
  | _, _ => none

/-- The values field `i`'s domain is instantiated at, in telescope order:
the parameters as `bvar nP, …, bvar 1`, the fields before `i` as the
subject's projections `.proj T j (bvar 0)`. -/
def projBodyArgs (T : Name) (nP i : Nat) : Array Expr :=
  (Array.range nP).map (fun k => mkBvar (nP - k)) ++
    (Array.range i).map (fun j => .proj T j (mkBvar 0))

/-- **Twin of `structProjBodies`' field `i`**: field `i`'s domain in the
constructor type, its parameters and earlier fields instantiated in one walk
by `projBodyArgs` (con-leche's telescope walk substitutes them one binder at
a time, to the same term). -/
def projBodyAt (T : Name) (nP i : Nat) (cty : Expr) : Option Expr :=
  (binderDom (nP + i) cty).map (·.instRevI (projBodyArgs T nP i))

/-- **Twin of `structProjBodiesGoC`**: one walk of the field telescope, threading the values
the next domain is instantiated at (`vs`: the parameters' variables, then the earlier fields'
projections, in telescope order, `projBodyArgs`); field `i`'s domain instantiated once. -/
def structProjBodiesGo (T : Name) (vs : Array Expr) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE _ fdom body _ =>
    (structProjBodiesGo T (vs.push (.proj T i (mkBvar 0))) k (i + 1) body).map
      (fdom.instRevI vs :: ·)
  | k + 1, i, .mdata _ e => structProjBodiesGo T vs (k + 1) i e
  | _ + 1, _, _ => none

/-- **Twin of `structProjBodiesC`**: every field's body in one walk of the constructor's
telescope (the block check's `checkBlockTablesC` reads them all); field `i`'s is
`projBodyAt T nP i` (`structProjBodies_eq_fields`). -/
def structProjBodies (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match peelPis nP cty with
  | some r =>
    (structProjBodiesGo T ((Array.range nP).map fun k => mkBvar (nP - k)) nF 0 r).map List.toArray
  | none => none

/-- **Every projection body of `T`'s table is in range** (`EO.inRange`), the
table read as `findProj?` reads it.  Not a twin: `projBodyAt` instantiates
the parameters by `bvar`s, lifted unchecked, so a constructor type in range
can yield a body past C's bound (a binder nest about 10^6 deep); the
inductive check refuses that as an internal error (`checkInductiveC`), as
abstraction's range poison is one. -/
def FEnv.projBodiesInRange (fe : FEnv) (T : Name) : Bool :=
  match fe.find? T with
  | some (.inductInfo v) =>
    match v.ctors with
    | [c] =>
      if v.numIndices == 0 then
        match fe.find? c with
        | some (.ctorInfo cv) =>
          if hasPis (v.numParams + cv.numFields) cv.type then
            (List.range cv.numFields).all fun i =>
              match projBodyAt T v.numParams i cv.type with
              | some b => EO.inRange b
              | none => true
          else true
        | _ => true
      else true
    | _ => true
  | _ => true

/-- **Field `i`'s body is in range, and so are the parameter variables it is
built with.**  `projBodiesInRange` reads the bodies of the tables of an
environment; this is the block check's view of the same bodies, and the
bound on the parameter variables (`bvar nP` must be a term C can build) is
what reading `projBodyAt`'s instantiation needs beside it. -/
def projBodyOk (T : Name) (nP i : Nat) (cty : Expr) : Bool :=
  decide (nP ≤ EO.maxBVarIdx) && (projBodyAt T nP i cty).all EO.inRange

/-- **`projBodyOk` at every field of every structure of a generated block**:
for each one-constructor former of `consts` and its constructor in `consts`.
The inductive check refuses a block failing it as an internal error
(`checkInductiveC`), beside `projBodiesInRange`. -/
def projBodiesAllOk (consts : Array ConstantInfo) : Bool :=
  consts.all fun ci =>
    match ci with
    | .inductInfo v =>
      match v.ctors with
      | [c] =>
        consts.all fun cj =>
          match cj with
          | .ctorInfo cv =>
            cv.name != c ||
              (List.range cv.numFields).all fun i => projBodyOk v.name v.numParams i cv.type
          | _ => true
      | _ => true
    | _ => true

/-- Twin of `ProjEntry.typeAtI`: the body at the levels, the subject type's
arguments and the subject. -/
def ProjEntry.typeAtI (entry : ProjEntry) (us : List Level) (targs : List Expr) (pe : Expr) :
    Option Expr :=
  (projBodyAt entry.structName entry.numParams entry.idx entry.ctorType).bind fun body =>
    (EO.instLevelParamsChecked? body entry.levelParams us).map
      (·.instI (#[pe] ++ targs.toArray.reverse))

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
