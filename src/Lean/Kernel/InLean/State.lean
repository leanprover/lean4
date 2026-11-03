/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Basic
public import Lean.Util.CollectFVars

/-!
# InLean: the per-declaration state and the data con-leche stores at install

Task #451.  Twin of `ConLeche/Cached/StateC.lean`: the monad, the memo
maps of the six core entry points (with the eager tower's set swapped in
and out, task #361), the level memos, the persistent bulk-instantiation
memo, the lazy `(name, levels)` caches of stored constants.

Two things are new, both forced by Lean's data (rulings 2 and 3 of the
#451 DESIGN record):

* **Free variables.**  `Lean.Expr.fvar` carries an id only.  con-leche's
  free variable is a de Bruijn level *with* its type (nanoda's
  representation), so that opening the same binder at the same depth
  gives the same term and the memos hit.  Here `(depth, type)` is
  interned to an `FVarId` per declaration (`mkFVar`): equal pairs get
  equal ids, so the memos behave as con-leche's do.
* **Install-derived data on use.**  What con-leche's installer stores
  beside Lean's constants (`IndCaps`, the rule bits and firing modes,
  the projection tables) is computed here from Lean's `InductiveVal`,
  `ConstructorVal` and `RecursorVal` when first needed, and kept in a
  per-declaration memo (`St.caps`, `St.recs`, `St.tabs`).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## Install-derived data -/

/-- Twin of `ConLeche.IndCaps`, read off a Lean `InductiveVal` and its
constructors (`blockCapsAt`, `ConLeche/Kernel/Inductives/BlockInstall.lean`). -/
structure IndCaps where
  eta : Bool := false
  etaCtor : Name := .anonymous
  etaParams : Nat := 0
  etaFields : Nat := 0
  unitlike : Bool := false
  unitParams : Nat := 0
  ruleK : Bool := false
  sortZ : PropWhen := .ifAllZero []
  /-- The family's result sort (the projection tables' `structSort`). -/
  resSort : Level := .zero
  deriving Inhabited

/-- Twin of `ConLeche.RecRuleFire`. -/
inductive RecRuleFire where
  | plain
  | nested (lvls : List Level) (pins : Array Expr)
  deriving Inhabited

/-- Twin of `ConLeche.RecRule`, with the install-computed fields. -/
structure RecRule where
  ctor : Name
  nfields : Nat
  ctorParams : Nat
  fire : RecRuleFire
  rhs : Expr
  k : Bool := false
  eta : Bool := false
  deriving Inhabited

/-- Twin of `ConLeche.ConstantInfo.recInfo`: a recursor's rules and the
two sums the firing path reads.  `Quot.lift`/`Quot.ind` are read as
recursors over `Quot.mk`, as con-leche's pinned quotient block stores
them. -/
structure RecX where
  lps : List Name
  type : Expr
  majorIdx : Nat
  rulePrefix : Nat
  rules : Array RecRule
  deriving Inhabited

/-- Twin of `ConLeche.ProjTable`: the bodies by substitution, the guards
(the fields' sorts) inferred on first use, and only at a structure whose
sort is `Prop` (the only place they are read). -/
structure ProjTable where
  structName : Name
  levelParams : List Name
  numParams : Nat
  ctor : Name
  numFields : Nat
  structSort : Level
  bodies : Array Expr
  ctorType : Expr
  deriving Inhabited

/-- Twin of `ConLeche.ProjEntry`. -/
structure ProjEntry where
  structName : Name
  idx : Nat
  levelParams : List Name
  numParams : Nat
  ctor : Name
  numFields : Nat
  body : Expr
  fieldSort : Level
  structSort : Level
  deriving Inhabited

/-! ## The state -/

/-- Twin of `ModeMemos`. -/
structure ModeMemos where
  whnfCoreC : Std.HashMap Expr Expr := {}
  whnfCoreCheapC : Std.HashMap Expr Expr := {}
  whnfC : Std.HashMap Expr Expr := {}
  inferC : Std.HashMap Expr Expr := {}
  inferIOC : Std.HashMap Expr Expr := {}
  defeqC : Std.HashMap (Expr × Expr) Bool := {}

/-- Twin of `CState`, plus the free-variable table and the derived-data
memos. -/
structure St where
  constTyAt : Std.HashMap (Name × List Level) Expr := {}
  constValAt : Std.HashMap (Name × List Level) Expr := {}
  ruleRhsAt : Std.HashMap (Name × Name × List Level) Expr := {}
  whnfCoreC : Std.HashMap Expr Expr := {}
  whnfCoreCheapC : Std.HashMap Expr Expr := {}
  whnfC : Std.HashMap Expr Expr := {}
  inferC : Std.HashMap Expr Expr := {}
  inferIOC : Std.HashMap Expr Expr := {}
  defeqC : Std.HashMap (Expr × Expr) Bool := {}
  lsimpC : Std.HashMap Level Level := {}
  eqvC : Std.HashMap (Level × Level) Bool := {}
  instC : Std.HashMap (Expr × List Expr) Expr := {}
  eagerMemos : ModeMemos := {}
  /-- `(depth, type)` ↦ free-variable number (ruling 3). -/
  fvTab : Std.HashMap (Nat × Expr) Nat := {}
  /-- per free-variable number: its type -/
  fvTys : Array Expr := #[]
  /-- per free-variable number: its depth -/
  fvDeps : Array Nat := #[]
  /-- install-derived data, per declaration (ruling 2) -/
  caps : Std.HashMap Name (Option IndCaps) := {}
  recs : Std.HashMap Name (Option RecX) := {}
  tabs : Std.HashMap Name (Option ProjTable) := {}
  /-- a Prop structure's guard levels, per structure -/
  guards : Std.HashMap Name (Array Level) := {}
  /-- the inductive generator's local context (lane B): per free-variable
  number, the binder name and info its local was declared with -/
  fvNames : Std.HashMap Nat (Name × BinderInfo) := {}
  /-- the generator's context depth: the number of locals declared so far
  (each new local at its own depth; the core runs at this depth) -/
  gdepth : Nat := 0
  /-- fresh names for the nested-elimination locals (never seen by the core) -/
  nestCtr : Nat := 0

instance : Inhabited St := ⟨{}⟩

/-- The checking context: the environment the declaration is checked
in and its safety (official `m_definition_safety`). -/
structure Ctx where
  env : Kernel.Environment
  safety : DefinitionSafety := .safe
  /-- Measurement probe: which install-derived data memo is bypassed
  (`""`: none; `"caps"`, `"recs"`, `"tabs"`, `"all"`).  Results are the
  same either way; only the cost differs. -/
  probeNoMemo : String := ""
  /-- **The axiom policy** (task #451 lane D).  `false`, con-leche's: only
  the standard and compiler-trust axioms are accepted, any other axiom and
  any use of `sorryAx` declines.  `true`, the official kernel's: every
  axiom is accepted and `sorryAx` may be used (what Lean needs for
  ordinary use; the pinned axioms' shapes are still checked). -/
  coreAxioms : Bool := false
  /-- **STOPGAP (task #451 lane D, open design question).**  Core elaborates Init in source
  order, where a pinned Nat operation is declared before the Init lemmas its certificates
  mention.  When set, a pinned operation whose pin or certificate check declines is accepted
  anyway, and the literal fast path fires on it uncertified, as in the official kernel. -/
  uncertifiedNatOps : Bool := false

/-- The checker's monad (twin of `CheckCM`). -/
abbrev M := ReaderT Ctx (EStateM Err St)

@[inline] def throwInvalid (msg : String) : M α := throw (.invalid msg)
@[inline] def throwDeclined (msg : String) : M α := throw (.declined msg)
@[inline] def throwInternal (msg : String) : M α := throw (.internal msg)

@[inline] def findConst? (n : Name) : M (Option ConstantInfo) := do
  return (← read).env.find? n

/-! ## Free variables -/

def fvRoot : Name := `_inlean_fv

/-- The interned free variable at `depth` with type `ty`. -/
def mkFVar (depth : Nat) (ty : Expr) : M Expr :=
  modifyGet fun s =>
    match s.fvTab[(depth, ty)]? with
    | some n => (.fvar ⟨.num fvRoot n⟩, s)
    | none =>
      let n := s.fvTys.size
      let tab := s.fvTab
      let tys := s.fvTys
      let deps := s.fvDeps
      let s := { s with fvTab := {}, fvTys := #[], fvDeps := #[] }
      (.fvar ⟨.num fvRoot n⟩,
       { s with fvTab := tab.insert (depth, ty) n, fvTys := tys.push ty,
                fvDeps := deps.push depth })

@[inline] def fvNum? (id : FVarId) : Option Nat :=
  match id.name with
  | .num p n => if p == fvRoot then some n else none
  | _ => none

/-- An interned free variable's type and depth. -/
def fvarInfo? (id : FVarId) : M (Option (Expr × Nat)) := do
  match fvNum? id with
  | some n =>
    let s ← get
    match s.fvTys[n]?, s.fvDeps[n]? with
    | some ty, some d => return some (ty, d)
    | _, _ => return none
  | none => return none

/-- The free variables occurring in `e` (a memoised DAG walk,
`Lean.CollectFVars`). -/
def fvarsOf (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds

/-- Twin of `Expr.wscopedBC depth e`: every free variable of `e` lies
below `depth` (the types of interned variables are scoped by
construction). -/
def wscoped (depth : Nat) (e : Expr) : M Bool := do
  if !e.hasFVar then return true
  let s ← get
  return (fvarsOf e).all fun id =>
    match fvNum? id with
    | some n => match s.fvDeps[n]? with
      | some d => d < depth
      | none => false
    | none => false

/-- The free variables reachable from `e`, hereditarily through their
types (twin of `fvarLeavesC`: a nanoda free variable carries its type,
so con-leche's leaves include the variables of the annotations). -/
def fvarClosure (e : Expr) : M (Std.HashSet FVarId) := do
  let s ← get
  let mut seen : Std.HashSet FVarId := {}
  let mut todo := fvarsOf e
  while !todo.isEmpty do
    let id := todo.back!
    todo := todo.pop
    unless seen.contains id do
      seen := seen.insert id
      if let some n := fvNum? id then
        if let some ty := s.fvTys[n]? then
          todo := todo ++ fvarsOf ty
  return seen

/-- Twin of `Expr.leafGuard fab base`: the free variables of `fab` are
among `base`'s, hereditarily (`leavesSubC (fvarLeavesC base) fab`). -/
def leafGuard (fab base : Expr) : M Bool := do
  if !fab.hasFVar then return true
  let bs ← fvarClosure base
  return (fvarsOf fab).all bs.contains

/-! ## Syntactic operations (the `*M` wrappers) -/

/-- Twin of `instListM`: bulk instantiation (innermost first) under the
persistent result memo. -/
def instListM (e : Expr) (vs : List Expr) : M Expr :=
  if !e.hasLooseBVars then pure e else
  modifyGet fun s =>
    match s.instC[(e, vs)]? with
    | some r => (r, s)
    | none =>
      let mp := s.instC
      let s := { s with instC := {} }
      let r := e.instantiate vs.toArray
      (r, { s with instC := mp.insert (e, vs) r })

/-! ## Level operations -/

/-- Twin of `isEquivLM`: level equivalence under the result memo. -/
def isEquivLM (l r : Level) : M (Option Bool) :=
  if l == r then pure (some true) else
  modifyGet fun s =>
    match s.eqvC[(l, r)]? with
    | some b => (some b, s)
    | none =>
      let mp := s.lsimpC
      let ec := s.eqvC
      let s := { s with lsimpC := {}, eqvC := {} }
      let (ls, mp) :=
        match mp[l]? with
        | some x => (x, mp)
        | none => let x := Lvl.simplify l; (x, mp.insert l x)
      let (rs, mp) :=
        match mp[r]? with
        | some x => (x, mp)
        | none => let x := Lvl.simplify r; (x, mp.insert r x)
      if ls == rs then
        (some true, { s with lsimpC := mp, eqvC := ec.insert (l, r) true })
      else
        match Lvl.leqCore Lvl.defaultFuel ls rs 0 with
        | some false =>
          (some false, { s with lsimpC := mp, eqvC := ec.insert (l, r) false })
        | some true =>
          match Lvl.leqCore Lvl.defaultFuel rs ls 0 with
          | some b => (some b, { s with lsimpC := mp, eqvC := ec.insert (l, r) b })
          | none => (none, { s with lsimpC := mp, eqvC := ec })
        | none => (none, { s with lsimpC := mp, eqvC := ec })

/-- Twin of `liftFueled`: an undecided level comparison is an error. -/
@[inline] def liftLevel (o : Option Bool) : M Bool :=
  match o with
  | some b => pure b
  | none => throwInternal "fuel exhausted: level comparison"

def isEquivL (l r : Level) : M Bool := do liftLevel (← isEquivLM l r)

/-- Twin of `isEquivListLM`. -/
def isEquivListLM : List Level → List Level → M (Option Bool)
  | [], [] => pure (some true)
  | l :: ls, r :: rs => do
    match ← isEquivLM l r with
    | none => pure none
    | some false => pure (some false)
    | some true => isEquivListLM ls rs
  | _, _ => pure (some false)

def isEquivListL (ls rs : List Level) : M Bool := do liftLevel (← isEquivListLM ls rs)

/-! ## Environment readers -/

/-- The level parameters, type and (for a definition) value of a
constant. -/
def ConstantInfo.defnValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | _ => none

/-- Is the expression headed by a constructor (twin of `isCtorAppC`;
`Quot.mk` is the quotient block's constructor in con-leche's pin)? -/
def isCtorApp (env : Kernel.Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const cn _ =>
    match env.find? cn with
    | some (.ctorInfo _) => true
    | some (.quotInfo q) => q.kind == .ctor
    | _ => false
  | _ => false

/-- A constructor's parameter and field counts (`Quot.mk`: 2 and 1). -/
def ctorCounts? (env : Kernel.Environment) (c : Name) : Option (Nat × Nat) :=
  match env.find? c with
  | some (.ctorInfo v) => some (v.numParams, v.numFields)
  | some (.quotInfo q) => if q.kind == .ctor then some (2, 1) else none
  | _ => none

/-- Twin of `headHintC`. -/
def headHint (env : Kernel.Environment) (e : Expr) : ReducibilityHints :=
  match e.getAppFn with
  | .const nm _ =>
    match env.find? nm with
    | some (.defnInfo v) => v.hints
    | _ => .opaque
  | _ => .opaque

/-- Twin of `unfoldableHeadC`. -/
def unfoldableHead (env : Kernel.Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const nm us =>
    match env.find? nm with
    | some (.defnInfo v) => us.length == v.levelParams.length
    | _ => false
  | _ => false

/-- Twin of `sameConstHeadsC`. -/
def sameConstHeads (a b : Expr) : Bool :=
  match a, b with
  | .app f₁ _, .app f₂ _ =>
    match f₁.getAppFn, f₂.getAppFn with
    | .const n₁ _, .const n₂ _ => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- Twin of `rawNatLitC?`. -/
def rawNatLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .const c [] => if c == natZeroName then some 0 else none
  | _ => none

/-- Twin of `etaCtorShapeC`. -/
def etaCtorShape (env : Kernel.Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
    match ctorCounts? env c with
    | some (cnP, cnF) => e.getAppNumArgs == cnP + cnF
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

/-! ## Literal guards (twins of `natLitSupported`/`strLitSupported`) -/

/-- `e` without `mdata` (the literal guards compare stored types
syntactically, as con-leche's do on its mdata-free terms). -/
partial def stripMDataS (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMDataS b)
    | _ => none

/-- A guard on a stored type, raw first and `mdata`-stripped only on a
mismatch (the guards run on the hot path; Lean's stored types rarely
carry `mdata`). -/
@[inline] def tyOk (f : Expr → Bool) (ty : Expr) : Bool := f ty || f (stripMDataS ty)

def natIndOk : Option ConstantInfo → Bool
  | some (.inductInfo v) => v.levelParams.isEmpty && v.type == .sort (.succ .zero)
  | _ => false

def natZeroOk : Option ConstantInfo → Bool
  | some (.ctorInfo v) => v.levelParams.isEmpty && tyOk (· == .const natName []) v.type
  | _ => false

def natSuccOk : Option ConstantInfo → Bool
  | some (.ctorInfo v) => v.levelParams.isEmpty && tyOk (fun
      | .forallE _ (.const c1 []) (.const c2 []) _ => c1 == natName && c2 == natName
      | _ => false) v.type
  | _ => false

def natLitSupported (env : Kernel.Environment) : Bool :=
  natIndOk (env.find? natName) && natZeroOk (env.find? natZeroName) &&
    natSuccOk (env.find? natSuccName)

/-- A guard on a stored constant's level parameters and type. -/
@[inline] def ciOk (f : List Name → Expr → Bool) : Option ConstantInfo → Bool
  | some ci => tyOk (f ci.levelParams) ci.type
  | none => false

def stringTyOk : Option ConstantInfo → Bool :=
  ciOk fun lps ty => lps.isEmpty && ty == .sort (.succ .zero)

def listTyOk : Option ConstantInfo → Bool :=
  ciOk fun
    | [p], .forallE _ (.sort u1) (.sort u2) _ => u1 == .succ (.param p) && u2 == .succ (.param p)
    | _, _ => false

def listNilTyOk : Option ConstantInfo → Bool :=
  ciOk fun
    | [p], .forallE _ (.sort u1) (.app (.const l1 us1) (.bvar 0)) _ =>
      u1 == .succ (.param p) && l1 == listName && us1 == [.param p]
    | _, _ => false

def listConsTyOk : Option ConstantInfo → Bool :=
  ciOk fun
    | [p], .forallE _ (.sort u1)
        (.forallE _ (.bvar 0)
          (.forallE _ (.app (.const l1 us1) (.bvar 1))
            (.app (.const l2 us2) (.bvar 2)) _) _) _ =>
      u1 == .succ (.param p) && l1 == listName && l2 == listName &&
        us1 == [.param p] && us2 == [.param p]
    | _, _ => false

def charOfNatTyOk : Option ConstantInfo → Bool :=
  ciOk fun
    | [], .forallE _ (.const c1 []) (.const c2 []) _ => c1 == natName && c2 == charName
    | _, _ => false

def stringOfListTyOk : Option ConstantInfo → Bool :=
  ciOk fun
    | [], .forallE _ (.app (.const l1 us1) (.const c1 [])) (.const c2 []) _ =>
      l1 == listName && us1 == [.zero] && c1 == charName && c2 == stringName
    | _, _ => false

def strLitSupported (env : Kernel.Environment) : Bool :=
  natLitSupported env &&
    stringTyOk (env.find? stringName) &&
    stringOfListTyOk (env.find? stringOfListName) &&
    listTyOk (env.find? listName) &&
    listNilTyOk (env.find? listNilName) &&
    listConsTyOk (env.find? listConsName) &&
    stringTyOk (env.find? charName) &&
    charOfNatTyOk (env.find? charOfNatName)

/-- Twin of `natOpStoredF`. -/
def natOpStored (env : Kernel.Environment) (c : Name) (uncertified : Bool := false) : Bool :=
  match env.find? c with
  | some (.defnInfo _) => true
  -- STOPGAP (`Ctx.uncertifiedNatOps`): a `module` importer sees a non-exposed pinned operation
  -- (`Nat.land`/`lor`/`xor`/`gcd`) as an axiom; its certificate was checked in its home module
  | some (.axiomInfo _) | some (.opaqueInfo _) => uncertified
  | _ => false

/-- Twin of `natLitToConstructor`. -/
def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const natZeroName []
  | k + 1 => .app (.const natSuccName []) (.lit (.natVal k))

/-- Twin of `strLitToConstructor`. -/
def strLitToConstructor (s : String) : Expr :=
  .app (.const stringOfListName []) <|
    s.toList.foldr
      (init := .app (.const listNilName [.zero]) (.const charName []))
      fun c e =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e

/-- The official kernel's default bound on a computed numeral (`LEAN_NAT_MAX_SIZE`, 128 MB;
the environment variable is not read). -/
def natMaxBytes : Nat := 128 * 1024 * 1024

/-- The official kernel's guards on a literal computation (`reduce_pow`, `reduce_bin_nat_op`):
a refusal message where the official kernel throws.  Without them a huge exponent or shift
falls through to unfolding the operation structurally and exhausts the native stack. -/
def natOpRefusal (c : Name) (a b : Nat) : Option String :=
  let tooBig := "the kernel refused a `Nat` numeral because its size exceeds the maximum"
  if c == natPowName then
    if b ≥ 2 ^ 32 then
      some "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer"
    else if a > 1 && (a.log2 + 1) * b > natMaxBytes * 8 then
      some "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size"
    else none
  else if c == natShiftLeftName then
    if b ≥ 2 ^ 32 then
      some "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer"
    else if a != 0 && a.log2 + 1 + b > natMaxBytes * 8 then some tooBig
    else none
  else if c == natMulName then
    if a.log2 + b.log2 + 2 > natMaxBytes * 8 then some tooBig else none
  else none

/-- Twin of `natOpResult`. -/
def natOpResult (c : Name) (a b : Nat) : Option Expr :=
  if c == natPredName then some (.lit (.natVal (a - 1)))
  else if c == natAddName then some (.lit (.natVal (a + b)))
  else if c == natSubName then some (.lit (.natVal (a - b)))
  else if c == natMulName then some (.lit (.natVal (a * b)))
  else if c == natPowName then
    if b > 16777216 then
      if a ≤ 1 then some (.lit (.natVal (if a == 0 && b != 0 then 0 else 1))) else none
    else some (.lit (.natVal (a ^ b)))
  else if c == natDivName then some (.lit (.natVal (a / b)))
  else if c == natModName then some (.lit (.natVal (a % b)))
  else if c == natGcdName then some (.lit (.natVal (Nat.gcd a b)))
  else if c == natLandName then some (.lit (.natVal (Nat.land a b)))
  else if c == natLorName then some (.lit (.natVal (Nat.lor a b)))
  else if c == natXorName then some (.lit (.natVal (Nat.xor a b)))
  else if c == natShiftLeftName then some (.lit (.natVal (Nat.shiftLeft a b)))
  else if c == natShiftRightName then some (.lit (.natVal (Nat.shiftRight a b)))
  else if c == natBeqName then
    some (.const (if a == b then boolTrueName else boolFalseName) [])
  else if c == natBleName then
    some (.const (if a ≤ b then boolTrueName else boolFalseName) [])
  else none

/-! ## Small expression predicates (twins of `ConLeche/Kernel/Core.lean`'s) -/

def isEagerReduce : Expr → Bool
  | .app (.app (.const c _) _) _ => c == eagerReduceName
  | _ => false

def isBoolTrue : Expr → Bool
  | .const c [] => c == boolTrueName
  | _ => false

def isNatZero : Expr → Bool
  | .lit (.natVal 0) => true
  | .const c [] => c == natZeroName
  | _ => false

def natPred? : Expr → Option Expr
  | .lit (.natVal (n + 1)) => some (.lit (.natVal n))
  | .app (.const c []) x => if c == natSuccName then some x else none
  | _ => none

def headIsProj (e : Expr) : Bool :=
  match e.getAppFn with
  | .proj .. => true
  | _ => false

/-- Twin of `Expr.ioNeutral`. -/
def ioNeutral (e : Expr) : Bool :=
  match e.getAppFn with
  | .lam .. | .letE .. | .bvar _ => false
  | _ => true

/-- Twin of `Expr.peelPis`: the residual after `k` syntactic ∀ binders. -/
def peelPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ _ b _ => peelPis k b
  | _ + 1, _ => none

/-- The result of a ∀ telescope (twin of `Expr.piResult`). -/
def piResult : Expr → Expr
  | .forallE _ _ b _ => piResult b
  | e => e

/-- Twin of `teleArityOk`. -/
def teleArityOk (ty : Expr) (n : Nat) : Bool := (peelPis n ty).isSome

/-- Twin of `piResidual`: instantiate a ∀ telescope along `args` (bulk,
with a raw `bvar` residual flushed and re-entered). -/
partial def piResidualGo (args : Array Expr) (acc : Array Expr) (e : Expr) (i : Nat) :
    Option Expr :=
  if h : i < args.size then
    match e with
    | .forallE _ _ b _ => piResidualGo args (acc.push args[i]) b (i + 1)
    | .bvar .. =>
      if acc.isEmpty then none else piResidualGo args #[] (e.instantiateRev acc) i
    | _ => none
  else some (e.instantiateRev acc)

def piResidual (e : Expr) (args : Array Expr) : Option Expr := piResidualGo args #[] e 0

end Lean.Kernel.InLean
