/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.State
public import Lean.Kernel.InLean.Pins

/-!
# InLean: the install-derived data, read on use

Task #451, ruling 2.  What con-leche's installer stores beside the
constants (OVERVIEW §13: `IndCaps`, the rule bits `k`/`eta`, the rule's
`ctorParams` and firing mode, `majorIdx`/`rulePrefix`, the projection
tables' bodies) is computed here from Lean's own constants, by the
installer's own formulas:

* `capsOf` — twin of `blockCapsAt` (`Inductives/BlockInstall.lean`),
  with official's `is_rec` read from `InductiveVal.isRec` (the same
  notion, `blockRawRec`) and the result sort read off the stored former
  (`storedTele`: a syntactic telescope, else definitions at its head
  unfolded);
* `recOf` — twin of `tgtStoredRules`/`storedMajor`
  (`Cached/StoredInstall.lean`): a rule's constructor parameter count,
  its K and η bits (`recRuleKOf`, `recRuleEtaOf`) and its firing mode,
  `.nested` at the stored major domain's instantiation when the major is
  not a member of the recursor's block (`auxRuleFire`); `Quot.lift` and
  `Quot.ind` as the pinned quotient block's recursors;
* `projTableOf` — twin of `structProjBodiesC` (`Cached/CheckerC.lean`):
  the projection bodies by substitution, at every index-free
  one-constructor inductive (`storedTables`).  The guards need inference
  and live in the core (`InLean/Core.lean`, `projGuards`).

Each is memoised per declaration (`St.caps`, `St.recs`, `St.tabs`).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- The result sort of a former's type after `n` binders (twin of
`storedTele`'s sort): the syntactic telescope, with a definition at a
non-∀ head unfolded (δ then β, `fuel` times) — the reduced telescope
official's `whnf` loop reads at a def-headed former. -/
def readResSort (env : Kernel.Environment) : Nat → Nat → Expr → Option Level
  | _, 0, .sort s => some s
  | fuel, n + 1, .forallE _ _ b _ => readResSort env fuel n b
  | fuel + 1, n, e =>
    match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.defnInfo v) =>
        if us.length == v.levelParams.length then
          readResSort env fuel n ((v.value.instantiateLevelParams v.levelParams us).beta e.getAppArgs)
        else none
      | _ => none
    | _ => none
  | 0, _, _ => none

/-- The inductive a constructor's type ends in. -/
def ctorInductive? (ty : Expr) : Option Name :=
  match (piResult ty).getAppFn with
  | .const T _ => some T
  | _ => none

/-- Twin of `blockCapsAt` at a Lean inductive. -/
def capsOfInduct (env : Kernel.Environment) (v : InductiveVal) : IndCaps :=
  let resSort? := readResSort env 16 (v.numParams + v.numIndices) v.type
  let resSort := resSort?.getD .zero
  -- an unreadable sort reads "maybe `Prop`" and grants nothing (the
  -- checked install would reject the block)
  let sortZ := match resSort? with
    | some s => Lvl.zeronessOf s
    | none => .ifAllZero []
  let isProp := match resSort? with
    | some s => Lvl.isZero s
    | none => true
  let readable := resSort?.isSome
  match v.ctors with
  | [c] =>
    let nF := match env.find? c with
      | some (.ctorInfo cv) => cv.numFields
      | _ => 0
    let isRec := v.isRec
    { eta := readable && v.numIndices == 0 && !isProp && !isRec
      etaCtor := c
      etaParams := v.numParams
      etaFields := nF
      unitlike := readable && v.numIndices == 0 && nF == 0 && !isRec
      unitParams := v.numParams
      ruleK := readable && v.all.length == 1 && nF == 0 && isProp
      sortZ := sortZ
      resSort := resSort }
  | _ => { sortZ := sortZ, resSort := resSort }

/-- The capabilities of `T`: an inductive's (`capsOfInduct`), `Quot`'s
pinned ones (`sortZ` of `Sort u`), none otherwise. -/
def probeOff (which : String) : M Bool := do
  let p := (← read).probeNoMemo
  return p == which || p == "all"

def capsOf (T : Name) : M (Option IndCaps) := do
  if !(← probeOff "caps") then
    if let some c := (← get).caps[T]? then return c
  let env := (← read).env
  let r : Option IndCaps := match env.find? T with
    | some (.inductInfo v) => some (capsOfInduct env v)
    | some (.quotInfo q) =>
      if q.kind == .type then some { sortZ := Lvl.zeronessOf BasisDSL.u, resSort := BasisDSL.u }
      else none
    | _ => none
  modify fun s =>
    let mp := s.caps
    let s := { s with caps := {} }
    { s with caps := mp.insert T r }
  return r

/-- A constructor's inductive and its capabilities (twin of the
`find? ctor`/`find? T` pair of `recRuleKOf`/`recRuleEtaOf`). -/
def ctorCaps? (c : Name) : M (Option (ConstantInfo × ConstantInfo × IndCaps)) := do
  let env := (← read).env
  match env.find? c with
  | some ci =>
    match ctorInductive? ci.type with
    | some T =>
      match env.find? T, ← capsOf T with
      | some ti, some caps => return some (ci, ti, caps)
      | _, _ => return none
    | none => return none
  | none => return none

/-- Twin of `recRuleKOf`. -/
def recRuleKOf (c : Name) : M Bool := do
  match ← ctorCaps? c with
  | some (_, _, caps) =>
    match ctorCounts? (← read).env c with
    | some (_, nF) => return caps.ruleK && nF == 0
    | none => return false
  | none => return false

/-- Twin of `recRuleEtaOf`. -/
def recRuleEtaOf (c : Name) : M Bool := do
  match ← ctorCaps? c with
  | some (ci, ti, caps) => return caps.eta && caps.etaCtor == c && ci.levelParams == ti.levelParams
  | none => return false

/-- The stored major domain of a recursor type with `mI` binders before
the major, its loose bound variables lowered into the rule-prefix scope
(`rP` binders): the twin of `storedMajor`'s opening at the prefix and
`auxRuleFire`'s `abstractPrefix`.  `bvar j` of a pin is prefix binder
`rP - 1 - j`. -/
def majorDomain? (ty : Expr) (mI : Nat) : Option Expr :=
  match peelPis mI ty with
  | some (.forallE _ dom _ _) => some dom
  | _ => none

/-- Twin of the stored install's recursor reading (`storedRecs` /
`tgtStoredRules`) at a Lean `RecursorVal`. -/
def recOfRecursor (rv : RecursorVal) : M (Option RecX) := do
  let env := (← read).env
  let mI := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
  let rP := rv.numParams + rv.numMotives + rv.numMinors
  -- the major: a member of the block (`.plain`), or an outside container
  -- at the stored domain's levels and parameters (`.nested`)
  let fire : RecRuleFire :=
    match majorDomain? rv.type mI with
    | some dom =>
      match dom.getAppFn with
      | .const I us =>
        if rv.all.contains I then .plain else
        match env.find? I with
        | some (.inductInfo iv) =>
          let ds := (dom.getAppArgs.extract 0 iv.numParams).map fun d =>
            d.lowerLooseBVars (mI - rP) (mI - rP)
          .nested us ds
        | _ => .plain
      | _ => .plain
    | none => .plain
  let mut rules : Array RecRule := #[]
  for r in rv.rules do
    let cP := match ctorCounts? env r.ctor with
      | some (p, _) => p
      | none => 0
    let k ← recRuleKOf r.ctor
    let eta ← recRuleEtaOf r.ctor
    rules := rules.push { ctor := r.ctor, nfields := r.nfields, ctorParams := cP, fire := fire,
                          rhs := r.rhs, k := k, eta := eta }
  return some { lps := rv.levelParams, type := rv.type, majorIdx := mI, rulePrefix := rP,
                rules := rules }

/-- The recursor view of `c` (twin of a stored `recInfo`): a Lean
recursor, or `Quot.lift`/`Quot.ind` as the pinned quotient block's. -/
def recOf (c : Name) : M (Option RecX) := do
  if !(← probeOff "recs") then
    if let some r := (← get).recs[c]? then return r
  let env := (← read).env
  let r : Option RecX ← match env.find? c with
    | some (.recInfo rv) => recOfRecursor rv
    | some (.quotInfo q) =>
      match q.kind with
      | .lift =>
        let rl : RecRule := { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
                              rhs := quotLiftRule }
        let rx : RecX := { lps := q.levelParams, type := q.type, majorIdx := 5, rulePrefix := 5,
                           rules := #[rl] }
        pure (some rx)
      | .ind =>
        let rl : RecRule := { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
                              rhs := quotIndRule }
        let rx : RecX := { lps := q.levelParams, type := q.type, majorIdx := 4, rulePrefix := 4,
                           rules := #[rl] }
        pure (some rx)
      | _ => pure none
    | _ => pure none
  modify fun s =>
    let mp := s.recs
    let s := { s with recs := {} }
    { s with recs := mp.insert c r }
  return r

/-- Twin of `structProjBodiesC`: replace the parameters by `bvar (nP -
k)` (the subject at `bvar 0`), then peel the fields, each field's
domain a body and the field replaced by `.proj T i (bvar 0)`. -/
def structProjBodies (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) := do
  let mut e := cty
  for k in [0:nP] do
    match e with
    | .forallE _ _ b _ => e := b.instantiate1 (.bvar (nP - k))
    | _ => none
  let mut bodies : Array Expr := #[]
  for i in [0:nF] do
    match e with
    | .forallE _ d b _ =>
      bodies := bodies.push d
      e := b.instantiate1 (.proj T i (.bvar 0))
    | _ => none
  return bodies

/-- The projection table of `T` (bodies only; twin of `storedTables`'
reading): every index-free one-constructor inductive. -/
def projTableOf (T : Name) : M (Option ProjTable) := do
  if !(← probeOff "tabs") then
    if let some t := (← get).tabs[T]? then return t
  let env := (← read).env
  let r : Option ProjTable ← match env.find? T with
    | some (.inductInfo v) =>
      match v.ctors, v.numIndices with
      | [c], 0 =>
        match env.find? c with
        | some (.ctorInfo cv) =>
          match structProjBodies T v.numParams cv.numFields cv.type with
          | some bodies => do
            let caps ← capsOf T
            pure (some { structName := T, levelParams := v.levelParams, numParams := v.numParams,
                         ctor := c, numFields := cv.numFields,
                         structSort := (caps.map (·.resSort)).getD .zero,
                         bodies := bodies, ctorType := cv.type })
          | none => pure none
        | _ => pure none
      | _, _ => pure none
    | _ => pure none
  modify fun s =>
    let mp := s.tabs
    let s := { s with tabs := {} }
    { s with tabs := mp.insert T r }
  return r

/-- Twin of `ProjEntry.typeAtI`: the body at the levels, the subject type's
arguments and the subject. -/
def ProjEntry.typeAt (entry : ProjEntry) (us : List Level) (targs : Array Expr)
    (pe : Expr) : Expr :=
  (entry.body.instantiateLevelParams entry.levelParams us).instantiate (#[pe] ++ targs.reverse)

/-! ## The head-symbol readers (twin of `ConLeche/Kernel/PropRead.lean`) -/

/-- Twin of `residualPW`. -/
def residualPW : Option Expr → Option PropWhen
  | some (.sort u) => some (Lvl.zeronessOf u)
  | _ => none

/-- Twin of `lamProj?`. -/
def lamProj? : Nat → Expr → Option (Nat × Nat)
  | k, .lam _ _ b _ => lamProj? (k + 1) b
  | k, .bvar j => if j < k then some (k, j) else none
  | _, _ => none

/-- Twin of `unwrapIdDefs`. -/
def unwrapIdDefs (env : Kernel.Environment) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match e.getAppFn with
    | .const c _ =>
      match env.find? c with
      | some (.defnInfo v) =>
        match lamProj? 0 v.value with
        | some (k, j) =>
          let args := e.getAppArgs
          if k ≤ args.size && args.size == k then
            unwrapIdDefs env fuel (args.getD (k - 1 - j) e)
          else e
        | none => e
      | _ => e
    | _ => e

/-- Twin of `peelPisW`. -/
def peelPisW (env : Kernel.Environment) : Nat → Expr → Option Expr
  | 0, e => some (unwrapIdDefs env 4 e)
  | k + 1, .forallE _ _ b _ => peelPisW env k b
  | k + 1, e =>
    match unwrapIdDefs env 4 e with
    | .forallE _ _ b _ => peelPisW env k b
    | _ => none

/-- Twin of `Expr.binderDom`. -/
def binderDom : Nat → Expr → Option Expr
  | 0, .forallE _ A _ _ => some A
  | k + 1, .forallE _ _ b _ => binderDom k b
  | _, _ => none

/-- The readers' context: the environment and the free-variable types. -/
structure PWCtx where
  env : Kernel.Environment
  fvTys : Array Expr

def PWCtx.fvarType? (c : PWCtx) (id : FVarId) : Option Expr :=
  match fvNum? id with
  | some n => c.fvTys[n]?
  | none => none

/-- Twin of `headTypePW`. -/
def headTypePW (c : PWCtx) (root : Expr) (d : Nat) : Expr → Nat → Option PropWhen
  | .const I us, n =>
    match c.env.find? I with
    | some ci =>
      if us.length == ci.levelParams.length then
        (residualPW (peelPisW c.env n ci.type)).map (Lvl.substPW ci.levelParams us)
      else none
    | none => none
  | .fvar id, n =>
    match c.fvarType? id with
    | some ty => residualPW (peelPisW c.env n ty)
    | none => none
  | .bvar i, n =>
    if i < d then
      match binderDom (d - 1 - i) root with
      | some D => residualPW (peelPisW c.env n D)
      | none => none
    else none
  | _, _ => none

/-- Twin of `typeSortPWGo`. -/
def typeSortPWGo (c : PWCtx) (root : Expr) : Expr → Nat → Option PropWhen
  | .forallE _ _ b _, d => typeSortPWGo c root b (d + 1)
  | .sort _, _ => some .never
  | R, d => headTypePW c root d R.getAppFn R.getAppNumArgs

/-- Twin of `typeSortPW`. -/
def typeSortPW (c : PWCtx) (T : Expr) : Option PropWhen := typeSortPWGo c T T 0

/-- Twin of `headProofPW`; the projection arm reads the table's body
(`projBody?`). -/
def headProofPW (c : PWCtx) (projBody? : Name → Nat → Option Expr) : Expr → Option PropWhen
  | .const n us =>
    match c.env.find? n with
    | some ci =>
      if us.length == ci.levelParams.length then
        (typeSortPW c ci.type).map (Lvl.substPW ci.levelParams us)
      else none
    | none => none
  | .fvar id =>
    match c.fvarType? id with
    | some ty => typeSortPW c ty
    | none => none
  | .sort _ | .forallE .. | .lit _ => some .never
  | .proj S i _ =>
    match projBody? S i with
    | some body =>
      match typeSortPW c body with
      | some pw => if pw.isNever then some pw else none
      | none => none
    | none => none
  | _ => none

/-- Twin of `proofPW`. -/
def proofPW (c : PWCtx) (projBody? : Name → Nat → Option Expr) : Expr → Option PropWhen
  | .lam _ _ b _ => proofPW c projBody? b
  | .letE _ _ _ b _ => proofPW c projBody? b
  | .app f _ => proofPW c projBody? f
  | .mdata _ e => proofPW c projBody? e
  | h => headProofPW c projBody? h

end Lean.Kernel.InLean
