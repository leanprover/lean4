/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Derived

/-!
# InLean: the checker core

Task #451.  Twin of `ConLeche/Cached/CoreC.lean` on `Lean.Expr`:
`whnfCore` (with the official `cheap_proj` flag), `whnf`, `infer` (full
grade), `inferIO` (official's `infer_only` grade), `defeq` and the eager
tower's `defeqE`, each memoised in `St`, in the official dispatch order
with con-leche's deviations (OVERVIEW §3: proof irrelevance before head
normalisation, opaque theorems, the K/structure/`And` rescues, the
verified mode's certificate families).

**One body, every mode.**  Every function takes the mode `μ`; what the
trusted mode omits is exactly what `μ.verifiedChecks` gates (the `certAt`
sites and the λ/η body-type comparisons).  The eager tower is the same
functions at `μ.toEager`, on their own memos (`withEagerMemos`).

**No fuel.**  con-leche's fuel exists for the proofs' induction and is
2^62 everywhere; here the recursion is `partial`, the loops iterate in
constant stack as con-leche's do.

**What differs from `CoreC` and why** (beyond the data, `Derived.lean`):
* `mdata` is looked through: `whnfCore` steps under it, `infer` infers
  under it (official `whnf_core`/`infer_type_core`); con-leche's `Expr`
  has no `mdata`.
* A free variable's type is the interned one (`St.fvTys`), its scope the
  interned depth (`St.fvDeps`).
* Inference of a constant at the full grade checks the declaration's
  safety against the constant's (official `infer_constant`); con-leche
  checks no unsafe declaration at all (it declines them).
* Substitution is core's: `instantiate`, `instantiateRev`, `abstractRange`,
  `instantiateLevelParams` (ruling 4).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- Twin of `WhnfStep`. -/
inductive WhnfStep where
  | done (e : Expr)
  | cont (e : Expr)

/-- Twin of `DeltaStep`. -/
inductive DeltaStep where
  | eq
  | diff
  | cont (a b : Expr)
  | unknown

/-- Twin of `LazyRes`. -/
inductive LazyRes where
  | verdict (v : Bool)
  | unknown (a b : Expr)

/-! ## The eager tower's memos (twin of `withEagerMemos`) -/

def St.modeMemos (s : St) : ModeMemos :=
  ⟨s.whnfCoreC, s.whnfCoreCheapC, s.whnfC, s.inferC, s.inferIOC, s.defeqC⟩

def St.enterEager (eager : Bool) (s : St) : Option ModeMemos × St :=
  if eager then (none, s) else
  let saved := s.modeMemos
  let em := s.eagerMemos
  let s := { s with whnfCoreC := {}, whnfCoreCheapC := {}, whnfC := {}, inferC := {},
                    inferIOC := {}, defeqC := {}, eagerMemos := {} }
  (some saved,
   { s with whnfCoreC := em.whnfCoreC, whnfCoreCheapC := em.whnfCoreCheapC,
            whnfC := em.whnfC, inferC := em.inferC, inferIOC := em.inferIOC,
            defeqC := em.defeqC })

def St.leaveEager (s : St) : Option ModeMemos → St
  | none => s
  | some saved =>
    let em := s.modeMemos
    let s := { s with whnfCoreC := {}, whnfCoreCheapC := {}, whnfC := {}, inferC := {},
                      inferIOC := {}, defeqC := {} }
    { s with eagerMemos := em,
             whnfCoreC := saved.whnfCoreC, whnfCoreCheapC := saved.whnfCoreCheapC,
             whnfC := saved.whnfC, inferC := saved.inferC, inferIOC := saved.inferIOC,
             defeqC := saved.defeqC }

@[inline] def withEagerMemos (μ : CheckMode) (x : M α) : M α := do
  let saved ← modifyGet (St.enterEager μ.eager)
  try
    let r ← x
    modify (·.leaveEager saved)
    pure r
  catch e =>
    modify (·.leaveEager saved)
    throw e

/-! ## Stored-constant caches (twins of `constTyAtM`, `constValAtM`, `ruleRhsAtM`) -/

def constTyAt (ci : ConstantInfo) (us : List Level) : M Expr := do
  if us.isEmpty then return ci.type
  let key := (ci.name, us)
  if let some i := (← get).constTyAt[key]? then return i
  let i := ci.type.instantiateLevelParams ci.levelParams us
  modify fun s =>
    let mp := s.constTyAt
    let s := { s with constTyAt := {} }
    { s with constTyAt := mp.insert key i }
  return i

def constValAt (n : Name) (lps : List Name) (v : Expr) (us : List Level) : M Expr := do
  if us.isEmpty then return v
  let key := (n, us)
  if let some i := (← get).constValAt[key]? then return i
  let i := v.instantiateLevelParams lps us
  modify fun s =>
    let mp := s.constValAt
    let s := { s with constValAt := {} }
    { s with constValAt := mp.insert key i }
  return i

def ruleRhsAt (c : Name) (rx : RecX) (rl : RecRule) (us : List Level) : M Expr := do
  if us.isEmpty then return rl.rhs
  let key := (c, rl.ctor, us)
  if let some i := (← get).ruleRhsAt[key]? then return i
  let i := rl.rhs.instantiateLevelParams rx.lps us
  modify fun s =>
    let mp := s.ruleRhsAt
    let s := { s with ruleRhsAt := {} }
    { s with ruleRhsAt := mp.insert key i }
  return i

/-! ## Pure guards over the environment -/

/-- Twin of `iotaArityOk`: a stored recursor applied to exactly
`majorIdx + 1` arguments at its own number of levels. -/
def iotaArityOk (env : Kernel.Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.recInfo rv) =>
      e.getAppNumArgs == rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 &&
        us.length == rv.levelParams.length
    | some (.quotInfo q) =>
      match q.kind with
      | .lift => e.getAppNumArgs == 6 && us.length == 2
      | .ind => e.getAppNumArgs == 5 && us.length == 1
      | _ => false
    | _ => false
  | _ => false

/-- Twin of `capsNeverZero`. -/
def capsNeverZero (lps : List Name) (us : List Level) (caps : IndCaps) : Bool :=
  (Lvl.substPW lps us caps.sortZ).isNever

/-- A constructor's level parameters, type and parameter count (`Quot.mk`
included). -/
def ctorView? (env : Kernel.Environment) (c : Name) : Option (List Name × Expr × Nat × Nat) :=
  match env.find? c with
  | some (.ctorInfo v) => some (v.levelParams, v.type, v.numParams, v.numFields)
  | some (.quotInfo q) => if q.kind == .ctor then some (q.levelParams, q.type, 2, 1) else none
  | _ => none

/-- Twin of `iotaCtorNeverProp`. -/
def iotaCtorNeverProp (cvjType : Expr) (us : List Level) : M Bool := do
  match ctorInductive? cvjType with
  | some T =>
    match (← read).env.find? T, ← capsOf T with
    | some ti, some caps =>
      return (ti.levelParams.length == us.length && capsNeverZero ti.levelParams us caps)
    | _, _ => return false
  | none => return false

/-- Twin of `recRuleK`. -/
def recRuleK (rules : Array RecRule) : Bool :=
  if h : rules.size = 1 then rules[0].k else false

/-- Twin of `projIndexedStructLike`. -/
def projIndexedStructLike (env : Kernel.Environment) (T sn : Name) (i nArgs : Nat) : Bool :=
  T == sn &&
    match env.find? T with
    | some (.inductInfo v) =>
      match v.ctors with
      | [c] =>
        v.numParams < nArgs &&
          match env.find? c with
          | some (.ctorInfo cv) => i < cv.numFields
          | _ => false
      | _ => false
    | _ => false

/-- Twin of `projMissError`. -/
def projMissError (env : Kernel.Environment) (hasTable : Bool) (T sn : Name) (i nArgs : Nat) :
    Err :=
  if hasTable then .invalid "projection index out of range"
  else if projIndexedStructLike env T sn i nArgs then
    .declined "projection on an indexed structure-like type"
  else .invalid "invalid projection: not a structure-like type, or no such field"

/-- Twin of `unknownConstError`. -/
def unknownConstError (n : Name) : Err :=
  if n == sorryAxName then .declined "use of the sorryAx axiom"
  else .invalid s!"unknown constant {n}"

/-- Does the table of `T` have `nF` fields (twin of `towerSlotsAllF`)? -/
def towerSlotsAll (T : Name) (nF : Nat) : M Bool := do
  match ← projTableOf T with
  | some t => return nF ≤ t.numFields
  | none => return nF == 0

/-- The projection body of `.proj S i`, for the head-symbol readers. -/
def projBody? (S : Name) (i : Nat) : M (Option Expr) := do
  match ← projTableOf S with
  | some t => return t.bodies[i]?
  | none => return none

/-- The head the readers' `proofPW` reaches. -/
partial def proofHead : Expr → Expr
  | .lam _ _ b _ => proofHead b
  | .letE _ _ _ b _ => proofHead b
  | .app f _ => proofHead f
  | .mdata _ e => proofHead e
  | h => h

/-- The readers' datum of `a` (`proofPW` with the projection body
fetched for the head). -/
def proofPWM (a : Expr) : M (Option PropWhen) := do
  let env := (← read).env
  let c : PWCtx := ⟨env, (← get).fvTys⟩
  match proofHead a with
  | .proj S i _ =>
    let b? ← projBody? S i
    return proofPW c (fun _ _ => b?) a
  | _ => return proofPW c (fun _ _ => none) a

/-- Twin of `notProofFast`. -/
def notProofFast (a : Expr) : M Bool := do
  match ← proofPWM a with
  | some pw => return !pw.isProp
  | none => return false

/-- Twin of `isProofFast`. -/
def isProofFast (a : Expr) : M Bool := do
  match ← proofPWM a with
  | some pw => return pw.isProp
  | none => return false

/-- Twin of `certAtI`: run the certificate at the verified modes. -/
@[inline] def certAt (μ : CheckMode) (c : M Bool) : M Bool :=
  if μ.verifiedChecks then c else pure true

/-- The memo wrapper for a unary entry point (twin of `memoEI`). -/
@[inline] def memoE (get' : St → Std.HashMap Expr Expr)
    (set' : St → Std.HashMap Expr Expr → St) (e : Expr) (f : Unit → M Expr) : M Expr := do
  match (get' (← get))[e]? with
  | some r => pure r
  | none =>
    let r ← f ()
    modify fun st =>
      let mp := get' st
      let st := set' st {}
      set' st (mp.insert e r)
    pure r

/-- The application-mismatch message, the terms shortened. -/
def appMismatchMsg (a ta dom : Expr) : String :=
  let sh (e : Expr) : String :=
    let s := toString e
    if s.length > 600 then (s.take 600).toString ++ "…" else s
  s!"application type mismatch: argument {sh a} has type {sh ta}, expected {sh dom}"

/-! ## The core -/

mutual

/-- Twin of the knot's `whnfCore` slot (the two `cheap_proj` modes under
two memos). -/
partial def whnfCore (μ : CheckMode) (cheap : Bool) (d : Nat) (e : Expr) : M Expr := do
  match e with
  | .sort _ | .fvar _ | .forallE .. | .lam .. | .lit _ => return e
  | _ =>
    if cheap then
      memoE (·.whnfCoreCheapC) (fun st mp => { st with whnfCoreCheapC := mp }) e
        fun _ => whnfCoreLoop μ true d e
    else
      memoE (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp }) e
        fun _ => whnfCoreLoop μ false d e

/-- Twin of `whnfCoreLoopI`. -/
partial def whnfCoreLoop (μ : CheckMode) (cheap : Bool) (d : Nat) (e : Expr) : M Expr := do
  match ← whnfCoreStep μ cheap d e with
  | .done v => pure v
  | .cont e' => whnfCoreLoop μ cheap d e'

/-- Twin of `whnfCoreStepI`. -/
partial def whnfCoreStep (μ : CheckMode) (cheap : Bool) (d : Nat) (e : Expr) : M WhnfStep := do
  match e with
  | .sort _ | .fvar _ | .forallE .. | .lam .. | .const .. | .lit _ => pure (.done e)
  | .mdata _ b => pure (.cont b)
  | .app .. =>
    let h := e.getAppFn
    let args := e.getAppArgs
    let v ← whnfCore μ cheap d h
    whnfApp μ d v args 0
  | .proj sn i pe =>
    let c ← if cheap then whnfCore μ true d pe else whnf μ d pe
    match ← reduceProjCore μ d sn i c with
    | some m' => pure (.cont m')
    | none => pure (.done e)
  | .letE _ _ v b _ => pure (.cont (b.instantiate1 v))
  | .bvar _ | .mvar _ => throwDeclined "whnf beyond the supported fragment"

/-- Twin of `whnfAppI`. -/
partial def whnfApp (μ : CheckMode) (d : Nat) (v : Expr) (args : Array Expr) (i : Nat) :
    M WhnfStep := do
  if h : i < args.size then
    let a := args[i]
    match v with
    | .lam _ _ body _ => betaPeel μ d body [a] args (i + 1)
    | _ =>
      let fa := Expr.app v a
      let env := (← read).env
      match ← (if iotaArityOk env fa then iotaRec μ d fa else pure none) with
      | some e'' => pure (.cont (mkAppRange e'' (i + 1) args.size args))
      | none => whnfApp μ d fa args (i + 1)
  else pure (.done v)

/-- Twin of `betaPeelI`. -/
partial def betaPeel (μ : CheckMode) (d : Nat) (t : Expr) (acc : List Expr) (args : Array Expr)
    (i : Nat) : M WhnfStep := do
  if h : i < args.size then
    match t with
    | .lam _ _ body _ => betaPeel μ d body (args[i] :: acc) args (i + 1)
    | _ =>
      let e' ← instListM t acc
      pure (.cont (mkAppRange e' i args.size args))
  else
    let e' ← instListM t acc
    pure (.cont e')

/-- Twin of `whnfBodyI`/`whnfLoopI`/`whnfStepI`, memoised. -/
partial def whnf (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  match e with
  | .sort _ | .fvar _ | .forallE .. | .lam .. | .lit _ => return e
  | _ => memoE (·.whnfC) (fun st mp => { st with whnfC := mp }) e fun _ => whnfLoop μ d e

partial def whnfLoop (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  let e₁ ← whnfCore μ false d e
  match ← reduceNat μ d e₁ with
  | some e₂ => whnfLoop μ d e₂
  | none =>
    match ← unfoldDefinition e₁ with
    | some e₂ => whnfLoop μ d e₂
    | none => pure e₁

/-- Twin of `unfoldDefinitionI`: a theorem never unfolds. -/
partial def unfoldDefinition (e : Expr) : M (Option Expr) := do
  match e.getAppFn with
  | .const n us =>
    match (← read).env.find? n with
    | some (.defnInfo v) =>
      if us.length == v.levelParams.length then
        let val ← constValAt n v.levelParams v.value us
        return some (mkAppN val e.getAppArgs)
      else return none
    | _ => return none
  | _ => return none

/-- Twin of `reduceNatI`. -/
partial def reduceNat (μ : CheckMode) (d : Nat) (e : Expr) : M (Option Expr) := do
  match e with
  | .app f₁ b =>
    match f₁ with
    | .const c [] =>
      let env := (← read).env
      if c == natSuccName && natLitSupported env then
        let w ← whnf μ d b
        match rawNatLit? w with
        | some n => return some (.lit (.natVal (n + 1)))
        | none => return none
      else return none
    | .app (.const cn []) a =>
      let env := (← read).env
      if (natOpNames.contains cn || natDivModNames.contains cn) && cn != natPredName &&
          natOpStored env cn then
        let w₁ ← whnf μ d a
        match rawNatLit? w₁ with
        | some n₁ =>
          let w₂ ← whnf μ d b
          match rawNatLit? w₂ with
          | some n₂ => return natOpResult cn n₁ n₂
          | none => return none
        | none => return none
      else if natDivModNames.contains cn && natLitSupported env then
        let w₁ ← whnf μ d a
        match rawNatLit? w₁ with
        | some _ =>
          let w₂ ← whnf μ d b
          match rawNatLit? w₂ with
          | some _ => throwDeclined s!"native Nat computation on literals ({cn})"
          | none => return none
        | none => return none
      else return none
    | _ => return none
  | _ => return none

/-- Twin of `litToCtorIfNatI`/`litMajorToCtorI`. -/
partial def litMajorToCtor (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  let env := (← read).env
  match e with
  | .lit (.strVal s) =>
    if strLitSupported env then whnf μ d (strLitToConstructor s) else pure e
  | .lit (.natVal n) => if natLitSupported env then pure (natLitToConstructor n) else pure e
  | _ => pure e

/-- Twin of `projLitToCtorI`. -/
partial def projLitToCtor (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  match e with
  | .lit (.strVal s) =>
    if strLitSupported (← read).env then whnf μ d (strLitToConstructor s) else pure e
  | _ => pure e

/-- **The guard levels of a `Prop` structure's projection table** (twin
of `storedGuards`: the fields' sorts by the constructor stage's walk,
then `structProjGuards`), computed on first use. -/
partial def projGuards (μ : CheckMode) (t : ProjTable) : M (Array Level) := do
  if let some g := (← get).guards[t.structName]? then return g
  let mut e := t.ctorType
  let mut fvs : Array Expr := #[]
  for k in [0:t.numParams] do
    match e with
    | .forallE _ dom b _ =>
      let fv ← mkFVar k (dom.instantiateRev fvs)
      fvs := fvs.push fv
      e := b
    | _ => throwInternal "projection guards: constructor telescope"
  let mut sorts : Array Level := #[]
  for j in [0:t.numFields] do
    match e with
    | .forallE _ dom b _ =>
      let domo := dom.instantiateRev fvs
      let s ← ensureSort μ (t.numParams + j) (← infer μ (t.numParams + j) domo)
      sorts := sorts.push s
      let fv ← mkFVar (t.numParams + j) domo
      fvs := fvs.push fv
      e := b
    | _ => throwInternal "projection guards: constructor telescope"
  -- `structProjGuards`: field `i`'s sort joined with the sorts of the
  -- earlier fields a later field uses
  let used : Array Bool := (Array.range t.numFields).map fun j =>
    match peelPis (t.numParams + j + 1) t.ctorType with
    | some rest => rest.hasLooseBVar 0
    | none => false
  let guards := (Array.range t.numFields).map fun i =>
    (List.range i).foldl
      (fun acc j => if used.getD j false then .max acc (sorts.getD j .zero) else acc)
      (sorts.getD i .zero)
  modify fun s =>
    let mp := s.guards
    let s := { s with guards := {} }
    { s with guards := mp.insert t.structName guards }
  return guards

/-- Twin of `Env.findProj?`: field `i`'s entry of `T`'s table, its guard
computed only at a `Prop` structure (the only place it is read). -/
partial def findProj? (μ : CheckMode) (T : Name) (i : Nat) : M (Option ProjEntry) := do
  match ← projTableOf T with
  | some t =>
    if i < t.numFields then
      let fs ← if Lvl.isZero t.structSort then
          pure ((← projGuards μ t).getD i .zero)
        else pure .zero
      return some { structName := T, idx := i, levelParams := t.levelParams,
                    numParams := t.numParams, ctor := t.ctor, numFields := t.numFields,
                    body := t.bodies.getD i default, fieldSort := fs,
                    structSort := t.structSort }
    else return none
  | none => return none

/-- Twin of `reduceProjCoreI`. -/
partial def reduceProjCore (μ : CheckMode) (d : Nat) (sn : Name) (i : Nat) (c : Expr) :
    M (Option Expr) := do
  let e' ← projLitToCtor μ d c
  match ← findProj? μ sn i with
  | some entry =>
    match e'.getAppFn with
    | .const k us =>
      let args := e'.getAppArgs
      if k == entry.ctor && i < entry.numFields &&
          args.size == entry.numParams + entry.numFields &&
          us.length == entry.levelParams.length && entryFireOk entry us then
        let arg := args.getD (entry.numParams + i) (.bvar 0)
        -- `projCertAt`
        if μ.verifiedChecks then
          match ctorView? (← read).env k with
          | some (_, ty, _, _) => if teleArityOk ty args.size then return some arg else return none
          | none => return none
        else return some arg
      else return none
    | _ => return none
  | none => return none

/-- Twin of `ProjEntry.fireOk`. -/
partial def entryFireOk (entry : ProjEntry) (us : List Level) : Bool :=
  !Lvl.isZero entry.structSort ||
    Lvl.isZero (Lvl.subst entry.levelParams us entry.fieldSort)

/-- Twin of `andRescueSlotsOf`. -/
partial def andRescueSlots (μ : CheckMode) (ctor : Name) (nP : Nat) (ust : List Level) : M Bool := do
  for j in [0:2] do
    match ← findProj? μ andName j with
    | some e =>
      unless e.ctor == ctor && e.numParams == nP && e.numFields == 2 && entryFireOk e ust do
        return false
    | none => return false
  return true

/-- Twin of `majorToCtorI`. -/
partial def majorToCtor (μ : CheckMode) (d : Nat) (rules : Array RecRule) (major : Expr) :
    M Expr := do
  let env := (← read).env
  if isCtorApp env major then return major
  if h : rules.size = 1 then
    let rl := rules[0]
    match ctorView? env rl.ctor with
    | some (cvjLps, cvjType, cnP, _) =>
      match (piResult cvjType).getAppFn with
      | .const T _ =>
        match env.find? T, ← capsOf T with
        | some cvT, some caps =>
          if rl.k then
            let tmaj ← whnf μ d (← inferIO μ d major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' == T && cvjLps.length == ust.length then
                let margs := tmaj.getAppArgs
                if cnP ≤ margs.size then
                  let fab := mkAppN (.const rl.ctor ust) (margs.extract 0 cnP)
                  if (← wscoped d fab) && !fab.hasLooseBVars && (← leafGuard fab major) then
                    -- official `to_cnstr_when_K` fabrication type check (both
                    -- modes); its proof irrelevance is a certificate family
                    let tfab ← inferIO μ d fab
                    if ← defeq μ d tmaj tfab then
                      if ← certAt μ (proofIrrel μ d fab major) then return fab
                      else return major
                    else return major
                  else return major
                else return major
              else return major
            | _ => return major
          else if rl.eta then
            let tmaj ← whnf μ d (← inferIO μ d major)
            match tmaj.getAppFn with
            | .const T' ust =>
              let margs := tmaj.getAppArgs
              if T' == T && margs.size == caps.etaParams &&
                  ust.length == cvT.levelParams.length &&
                  capsNeverZero cvT.levelParams ust caps &&
                  !reservedBasisNames.contains T && !reservedBasisNames.contains caps.etaCtor &&
                  (← towerSlotsAll T caps.etaFields) then
                let projs := (Array.range caps.etaFields).map fun j => Expr.proj T j major
                let fab := mkAppN (.const caps.etaCtor ust) (margs ++ projs)
                -- no certificate on the fabricated spine (task #342 L11b)
                if (← wscoped d fab) && !fab.hasLooseBVars && (← leafGuard fab major) then
                  return fab
                else return major
              else return major
            | _ => return major
          else if T == andName then
            -- the `And`-only rescue
            let tmaj ← whnf μ d (← inferIO μ d major)
            match tmaj.getAppFn with
            | .const T' ust =>
              let margs := tmaj.getAppArgs
              if T' == T && margs.size == cnP && cvjLps.length == ust.length &&
                  (← andRescueSlots μ rl.ctor cnP ust) then
                let projs := #[Expr.proj T 0 major, Expr.proj T 1 major]
                let fab := mkAppN (.const rl.ctor ust) (margs ++ projs)
                if (← wscoped d fab) && !fab.hasLooseBVars && (← leafGuard fab major) then
                  let tfab ← inferIO μ d fab
                  if ← defeq μ d tmaj tfab then
                    if ← certAt μ (proofIrrel μ d fab major) then return fab
                    else return major
                  else return major
                else return major
              else return major
            | _ => return major
          else return major
        | _, _ => return major
      | _ => return major
    | none => return major
  else return major

/-- Twin of `prepareMajorI`. -/
partial def prepareMajor (μ : CheckMode) (d : Nat) (rules : Array RecRule) (major : Expr) :
    M Expr := do
  let env := (← read).env
  if recRuleK rules then
    let majorK ← majorToCtor μ d rules major
    if isCtorApp env majorK then litMajorToCtor μ d majorK else pure majorK
  else
    let majorE ← match major with
      | .lit (.strVal _) => pure major
      | _ => majorToCtor μ d rules major
    if isCtorApp env majorE then pure majorE
    else
      let major₀ ← whnf μ d majorE
      let major₁ ← litMajorToCtor μ d major₀
      majorToCtor μ d rules major₁

/-- Twin of `defEqListI`. -/
partial def defEqList (μ : CheckMode) (d : Nat) (as bs : Array Expr) : M Bool := do
  if as.size != bs.size then return false
  for i in [0:as.size] do
    unless ← defeq μ d (as.getD i default) (bs.getD i default) do return false
  return true

/-- Twin of `iotaCertsFullIAux`. -/
partial def iotaCertsFull (μ : CheckMode) (d : Nat) (ty : Expr) (acc : List Expr)
    (args : Array Expr) (i : Nat) : M Bool := do
  if h : i < args.size then
    let arg := args[i]
    match ty with
    | .forallE _ dom body _ =>
      let dom' ← instListM dom acc
      let ta ← infer μ d arg
      if ← defeq μ d ta dom' then iotaCertsFull μ d body (arg :: acc) args (i + 1)
      else return false
    | .bvar _ =>
      if acc.isEmpty then return false
      let ty' ← instListM ty acc
      iotaCertsFull μ d ty' [] args i
    | _ => return false
  else return true

/-- Twin of `iotaIndexOkI`. -/
partial def iotaIndexOk (μ : CheckMode) (d : Nat) (mI rP cnP : Nat) (tyCtor : Expr)
    (margs idx : Array Expr) : M Bool := do
  if mI == rP then return true
  match piResidual tyCtor margs with
  | some residual => defEqList μ d (residual.getAppArgs.extract cnP) idx
  | none => return false

/-- Twin of `iotaRecI`. -/
partial def iotaRec (μ : CheckMode) (d : Nat) (e : Expr) : M (Option Expr) := do
  match e.getAppFn with
  | .const c us =>
    match ← recOf c with
    | some rx =>
      let args := e.getAppArgs
      let mI := rx.majorIdx
      let rP := rx.rulePrefix
      if args.size == mI + 1 && us.length == rx.lps.length &&
          (peelPis (mI + 1) rx.type).isSome then
        let major ← prepareMajor μ d rx.rules (args.getD mI (.bvar 0))
        match major.getAppFn with
        | .const cj usj =>
          match ctorView? (← read).env cj with
          | some (cvjLps, cvjType, _, _) =>
            match rx.rules.find? (·.ctor == cj) with
            | some rl =>
              let margs := major.getAppArgs
              if margs.size == rl.ctorParams + rl.nfields then
                -- the case-3 certificate family (task #342 L10, S5c)
                if ← certAt μ (do
                    let cmpLvls : List Level := match rl.fire with
                      | .nested lvls _ => lvls.map (Lvl.subst rx.lps us)
                      | .plain => cvjLps.map fun p => Lvl.subst rx.lps us (.param p)
                    if !rl.k && !(← iotaCtorNeverProp cvjType cmpLvls) then
                      if ← isEquivListL usj cmpLvls then
                        let cmpArgs : Array Expr := match rl.fire with
                          | .nested _ pins =>
                            pins.map fun p =>
                              (p.instantiateLevelParams rx.lps us).instantiateRev (args.extract 0 rP)
                          | .plain => args.extract 0 rl.ctorParams
                        if ← defEqList μ d (margs.extract 0 rl.ctorParams) cmpArgs then
                          let some ci := (← read).env.find? cj
                            | return false
                          let tyCtor ← constTyAt ci usj
                          if ← iotaCertsFull μ d tyCtor [] margs 0 then
                            iotaIndexOk μ d mI rP rl.ctorParams tyCtor margs
                              ((args.extract 0 mI).extract rP)
                          else return false
                        else return false
                      else return false
                    else return true) then
                  let rhs ← ruleRhsAt c rx rl us
                  return some (mkAppN rhs (args.extract 0 rP ++ margs.extract rl.ctorParams))
                else return none
              else return none
            | none => return none
          | none => return none
        | _ => return none
      else return none
    | none => return none
  | _ => return none

-- Inference

/-- Twin of `ensureSortI`. -/
partial def ensureSort (μ : CheckMode) (d : Nat) (e : Expr) : M Level := do
  match ← whnf μ d e with
  | .sort u => pure u
  | _ => throwInvalid "expected a sort"

/-- The full-grade inference slot (memoised). -/
partial def infer (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  memoE (·.inferC) (fun st mp => { st with inferC := mp }) e fun _ => inferBody μ false d e

/-- The infer-only slot (memoised apart, task #170). -/
partial def inferIO (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  memoE (·.inferIOC) (fun st mp => { st with inferIOC := mp }) e fun _ => inferBody μ true d e

@[inline] partial def inferG (μ : CheckMode) (io : Bool) (d : Nat) (e : Expr) : M Expr :=
  if io then inferIO μ d e else infer μ d e

/-- Twin of `inferBodyI` (`io = false`) and `inferBodyIOI` (`io = true`). -/
partial def inferBody (μ : CheckMode) (io : Bool) (d : Nat) (e : Expr) : M Expr := do
  match e with
  | .sort u => pure (.sort (.succ u))
  | .fvar id =>
    match ← fvarInfo? id with
    | some (ty, dep) =>
      if dep < d then pure ty else throwInvalid "free variable out of scope"
    | none => throwInvalid "unknown free variable"
  | .const n us =>
    let ctx ← read
    match ctx.env.find? n with
    | none => throw (unknownConstError n)
    | some ci =>
      -- `sorryAx` is in Lean's environment (the elaborator needs it), but a
      -- use declines, as con-leche's (it installs nothing for it)
      if n == sorryAxName && !ctx.coreAxioms then throwDeclined "use of the sorryAx axiom"
      unless us.length == ci.levelParams.length do
        throwInvalid s!"incorrect number of universe levels for {n}"
      if !io then
        -- official `infer_constant`'s safety checks
        if ci.isUnsafe && ctx.safety != .unsafe then
          throwInvalid s!"invalid declaration, it uses unsafe declaration '{n}'"
        if let .defnInfo v := ci then
          if v.safety == .partial && ctx.safety == .safe then
            throwInvalid s!"invalid declaration, safe declaration must not contain partial \
              declaration '{n}'"
      constTyAt ci us
  | .lit (.natVal _) =>
    if natLitSupported (← read).env then pure (.const natName [])
    else throwInvalid "Nat literal without the Nat basis declarations"
  | .lit (.strVal _) =>
    if strLitSupported (← read).env then pure (.const stringName [])
    else throwDeclined "string literals before the String support declarations"
  | .mdata _ b => inferG μ io d b
  | .forallE n ty body bi =>
    if io then
      let u ← ensureSort μ d (← inferIO μ d ty)
      let fv ← mkFVar d ty
      let v ← ensureSort μ (d + 1) (← inferIO μ (d + 1) (body.instantiate1 fv))
      let _ := (n, bi)
      pure (.sort (.imax u v))
    else inferPis μ d e 0 #[] []
  | .lam n ty body bi =>
    if io then
      let fv ← mkFVar d ty
      let bt ← inferIO μ (d + 1) (body.instantiate1 fv)
      pure (.forallE n ty (bt.abstract #[fv]) bi)
    else inferLams μ d e 0 #[] []
  | .app .. =>
    let h := e.getAppFn
    let args := e.getAppArgs
    if io then
      let tf ← inferIO μ d h
      inferSpineIO μ d tf #[] args 0
    else
      let tf ← infer μ d h
      inferSpine μ d tf #[] args 0
  | .proj sn i pe =>
    let te ← whnf μ d (← inferG μ io d pe)
    match te.getAppFn with
    | .const T us =>
      match ← findProj? μ T i with
      | some entry =>
        let targs := te.getAppArgs
        unless T == sn do
          throwInvalid "invalid projection: the node names another structure"
        unless targs.size == entry.numParams do
          throwInvalid "projection parameter mismatch"
        if us.length == entry.levelParams.length then
          if Lvl.isZero entry.structSort then
            unless Lvl.isZero (Lvl.subst entry.levelParams us entry.fieldSort) do
              throwInvalid "projection from a propositional structure must be a proposition"
          pure (entry.typeAt us targs pe)
        else throwDeclined "projection without a native entry"
      | none =>
        let hasTable := (← projTableOf T).isSome
        throw (projMissError (← read).env hasTable T sn i te.getAppNumArgs)
    | _ => throwInvalid "invalid projection: not a structure-like type, or no such field"
  | .letE _ ty v b _ =>
    if io then inferIO μ d (b.instantiate1 v)
    else
      let _ ← ensureSort μ d (← infer μ d ty)
      let tv ← infer μ d v
      unless ← defeq μ d tv ty do throwInvalid "let value type mismatch"
      infer μ d (b.instantiate1 v)
  | .bvar _ => throwDeclined "inferType beyond the supported fragment"
  | .mvar _ => throwInvalid "unexpected metavariable"

/-- Twin of `inferPisI` (the ∀-telescope loop): peel, check each opened
domain is a type, infer the bulk-opened leaf's sort, fold `imax`. -/
partial def inferPis (μ : CheckMode) (d : Nat) (t : Expr) (k : Nat) (fvs : Array Expr)
    (stk : List Level) : M Expr := do
  match t with
  | .forallE _ ty body _ =>
    let tyo := ty.instantiateRev fvs
    match ← whnf μ (d + k) (← infer μ (d + k) tyo) with
    | .sort u =>
      let fv ← mkFVar (d + k) tyo
      inferPis μ d body (k + 1) (fvs.push fv) (u :: stk)
    | _ => throwInvalid "expected a sort"
  | _ =>
    let ob := t.instantiateRev fvs
    match ← whnf μ (d + k) (← infer μ (d + k) ob) with
    | .sort v => pure (.sort (stk.foldl (fun acc u => .imax u acc) v))
    | _ => throwInvalid "expected a sort"

/-- Twin of `inferLamsI` (the λ-telescope loop): peel, check each opened
domain is a type, infer the bulk-opened leaf, rebuild with
`abstractRange`. -/
partial def inferLams (μ : CheckMode) (d : Nat) (t : Expr) (k : Nat) (fvs : Array Expr)
    (stk : List (Name × BinderInfo × Expr)) : M Expr := do
  match t with
  | .lam n ty body bi =>
    let tyo := ty.instantiateRev fvs
    match ← whnf μ (d + k) (← infer μ (d + k) tyo) with
    | .sort _ =>
      let fv ← mkFVar (d + k) tyo
      inferLams μ d body (k + 1) (fvs.push fv) ((n, bi, tyo) :: stk)
    | _ => throwInvalid "expected a sort"
  | _ =>
    let ob := t.instantiateRev fvs
    let bt ← infer μ (d + k) ob
    let mut cur := bt.abstractRange k fvs
    let mut j := k
    for (n, bi, tyo) in stk do
      j := j - 1
      cur := .forallE n (tyo.abstractRange j fvs) cur bi
    pure cur

/-- Twin of `defeqArgI`. -/
@[inline] partial def defeqArg (μ : CheckMode) (d : Nat) (a ta ty : Expr) : M Bool :=
  if isEagerReduce a then defeqE μ d ta ty else defeq μ d ta ty

/-- Twin of `inferSpineI`. -/
partial def inferSpine (μ : CheckMode) (d : Nat) (ty : Expr) (acc : Array Expr)
    (args : Array Expr) (i : Nat) : M Expr := do
  if h : i < args.size then
    let a := args[i]
    match ty with
    | .forallE _ dom body _ =>
      let dom' := dom.instantiateRev acc
      let ta ← infer μ d a
      unless ← defeqArg μ d a ta dom' do throwInvalid (appMismatchMsg a ta dom')
      inferSpine μ d body (acc.push a) args (i + 1)
    | _ =>
      match ← whnf μ d (ty.instantiateRev acc) with
      | .forallE _ dom body _ =>
        let ta ← infer μ d a
        unless ← defeqArg μ d a ta dom do throwInvalid (appMismatchMsg a ta dom)
        inferSpine μ d body #[a] args (i + 1)
      | _ => throwInvalid "function expected"
  else pure (ty.instantiateRev acc)

/-- Twin of `inferSpineIOI`. -/
partial def inferSpineIO (μ : CheckMode) (d : Nat) (ty : Expr) (acc : Array Expr)
    (args : Array Expr) (i : Nat) : M Expr := do
  if h : i < args.size then
    let a := args[i]
    match ty with
    | .forallE _ _ body _ => inferSpineIO μ d body (acc.push a) args (i + 1)
    | _ =>
      match ← whnf μ d (ty.instantiateRev acc) with
      | .forallE _ _ body _ => inferSpineIO μ d body #[a] args (i + 1)
      | _ => throwInvalid "function expected"
  else pure (ty.instantiateRev acc)

-- Definitional equality

/-- Twin of `proofIrrelI`. -/
partial def proofIrrel (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  match ← whnf μ d (← inferIO μ d (← inferIO μ d a)) with
  | .sort uT =>
    let okA ← isEquivL uT .zero
    match ← whnf μ d (← inferIO μ d (← inferIO μ d b)) with
    | .sort vT =>
      let okB ← isEquivL vT .zero
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- Twin of `propIrrelI`: the head-symbol readers first. -/
partial def propIrrel (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  if (← notProofFast a) || (← notProofFast b) then return false
  if (← isProofFast a) && (← isProofFast b) then return true
  proofIrrel μ d a b

/-- Twin of `structEtaCertWithI`. -/
partial def structEtaCertWith (μ : CheckMode) (d : Nat) (a b wtb : Expr) : M Bool := do
  let env := (← read).env
  match a.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.ctorInfo cvc) =>
      let aargs := a.getAppArgs
      if aargs.size == cvc.numParams + cvc.numFields then
        match wtb.getAppFn with
        | .const T us' =>
          match env.find? T, ← capsOf T with
          | some (.inductInfo cvT), some caps =>
            let targs := wtb.getAppArgs
            if caps.eta && caps.etaCtor == c && !reservedBasisNames.contains T &&
                !reservedBasisNames.contains c && targs.size == caps.etaParams &&
                us'.length == cvT.levelParams.length && cvc.levelParams == cvT.levelParams &&
                (← towerSlotsAll T caps.etaFields) then
              if ← isEquivListL us us' then
                if ← defEqList μ d (aargs.extract 0 caps.etaParams) targs then
                  let projs := (Array.range caps.etaFields).map fun j => Expr.proj T j b
                  defEqList μ d (aargs.extract caps.etaParams) projs
                else return false
              else return false
            else return false
          | _, _ => return false
        | _ => return false
      else return false
    | _ => return false
  | _ => return false

/-- Twin of `structEtaCertI`. -/
partial def structEtaCert (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  if etaCtorShape (← read).env a then
    let wtb ← whnf μ d (← inferIO μ d b)
    structEtaCertWith μ d a b wtb
  else return false

/-- Twin of `structUnitCertI`. -/
partial def structUnitCert (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  let wta ← whnf μ d (← inferIO μ d a)
  match wta.getAppFn with
  | .const T us' =>
    match (← read).env.find? T, ← capsOf T with
    | some (.inductInfo cvT), some caps =>
      if caps.unitlike && !reservedBasisNames.contains T &&
          wta.getAppNumArgs == caps.unitParams && us'.length == cvT.levelParams.length then
        let wtb ← whnf μ d (← inferIO μ d b)
        if wtb.isForall then return false
        defeq μ d wta wtb
      else return false
    | _, _ => return false
  | _ => return false

/-- Twin of `etaCertI`. -/
partial def etaCert (μ : CheckMode) (d : Nat) (ty₁ body₁ b : Expr) : M Bool := do
  if !ioNeutral b then return false
  match ← whnf μ d (← inferIO μ d b) with
  | .forallE _ ty₂ cod₂ _ =>
    if ← defeq μ d ty₂ ty₁ then
      let fv ← mkFVar d ty₁
      let b₁ := body₁.instantiate1 fv
      unless ← defeq μ (d + 1) b₁ (.app b fv) do return false
      if μ.verifiedChecks then
        let t₁ ← infer μ (d + 1) b₁
        unless ← defeq μ (d + 1) t₁ (cod₂.instantiate1 fv) do return false
      return true
    else return false
  | _ => return false

/-- Twin of `stuckIrrelI`. -/
partial def stuckIrrel (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  if ← structEtaCert μ d a b then return true
  if ← structEtaCert μ d b a then return true
  if ← structUnitCert μ d a b then return true
  proofIrrel μ d a b

/-- Twin of `defeqLamsI` (the λ/λ telescope; the body types compared at
the innermost level in the verified modes). -/
partial def defeqLams (μ : CheckMode) (d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) : M Bool := do
  unless ← defeq μ d ty₁ ty₂ do return false
  let fv ← mkFVar d ty₂
  let b₁ := body₁.instantiate1 fv
  let b₂ := body₂.instantiate1 fv
  match b₁, b₂ with
  | .lam _ ty₁' body₁' _, .lam _ ty₂' body₂' _ =>
    if b₁ == b₂ then return true
    defeqLams μ (d + 1) ty₁' body₁' ty₂' body₂'
  | _, _ =>
    unless ← defeq μ (d + 1) b₁ b₂ do return false
    if μ.verifiedChecks then
      let t₁ ← infer μ (d + 1) b₁
      let t₂ ← infer μ (d + 1) b₂
      unless ← defeq μ (d + 1) t₁ t₂ do return false
    return true

/-- Twin of `quickDefEqI`. -/
partial def quickDefEq (μ : CheckMode) (d : Nat) (a b : Expr) : M (Option Bool) := do
  if a == b then return some true
  match a, b with
  | .sort u, .sort v => return some (← isEquivL u v)
  | .lit l₁, .lit l₂ => return some (l₁ == l₂)
  | .forallE _ ty₁ body₁ _, .forallE _ ty₂ body₂ _ =>
    unless ← defeq μ d ty₁ ty₂ do return some false
    let fv ← mkFVar d ty₂
    unless ← defeq μ (d + 1) (body₁.instantiate1 fv) (body₂.instantiate1 fv) do
      return some false
    return some true
  | .lam _ ty₁ body₁ _, .lam _ ty₂ body₂ _ => return some (← defeqLams μ d ty₁ body₁ ty₂ body₂)
  | _, _ => return none

/-- Twin of `defeqOffsetI`. -/
partial def defeqOffset (μ : CheckMode) (d : Nat) (a b : Expr) : M (Option Bool) := do
  if isNatZero a && isNatZero b then return some true
  if a.isLit && b.isLit then return none
  match natPred? a, natPred? b with
  | some x, some y => return some (← defeq μ d x y)
  | _, _ => return none

/-- Twin of `tryUnfoldProjAppI`. -/
partial def tryUnfoldProjApp (μ : CheckMode) (d : Nat) (e : Expr) : M (Option Expr) := do
  if headIsProj e then
    let e' ← whnfCore μ false d e
    if e' == e then return none else return some e'
  else return none

/-- Twin of `deltaQuickI`. -/
partial def deltaQuick (μ : CheckMode) (d : Nat) (a b : Expr) : M DeltaStep := do
  match ← quickDefEq μ d a b with
  | some true => pure .eq
  | some false => pure .diff
  | none => pure (.cont a b)

/-- Twin of `lazyDeltaStepI`. -/
partial def lazyDeltaStep (μ : CheckMode) (d : Nat) (a b : Expr) : M DeltaStep := do
  let env := (← read).env
  match unfoldableHead env a, unfoldableHead env b with
  | false, false => pure .unknown
  | true, false =>
    match ← tryUnfoldProjApp μ d b with
    | some b₂ => deltaQuick μ d a b₂
    | none =>
      match ← unfoldDefinition a with
      | some a₂ => deltaQuick μ d (← whnfCore μ true d a₂) b
      | none => pure .unknown
  | false, true =>
    match ← tryUnfoldProjApp μ d a with
    | some a₂ => deltaQuick μ d a₂ b
    | none =>
      match ← unfoldDefinition b with
      | some b₂ => deltaQuick μ d a (← whnfCore μ true d b₂)
      | none => pure .unknown
  | true, true =>
    let ha := headHint env a
    let hb := headHint env b
    if hintLt hb ha then
      match ← unfoldDefinition a with
      | some a₂ => deltaQuick μ d (← whnfCore μ true d a₂) b
      | none => pure .unknown
    else if hintLt ha hb then
      match ← unfoldDefinition b with
      | some b₂ => deltaQuick μ d a (← whnfCore μ true d b₂)
      | none => pure .unknown
    else if ← (if hintSameRegular ha hb && sameConstHeads a b then defeqSpine μ d a b
        else pure false) then pure .eq
    else
      match ← unfoldDefinition a, ← unfoldDefinition b with
      | some a₂, some b₂ =>
        let a₃ ← whnfCore μ true d a₂
        let b₃ ← whnfCore μ true d b₂
        deltaQuick μ d a₃ b₃
      | _, _ => pure .unknown

/-- Twin of `defeqSpineI` (arguments last to first, official
`is_def_eq_args`). -/
partial def defeqSpine (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  match a.getAppFn, b.getAppFn with
  | .const n us, .const n' us' =>
    let aargs := a.getAppArgs
    let bargs := b.getAppArgs
    if n == n' && aargs.size == bargs.size then
      match ← isEquivListLM us us' with
      | some true => defEqList μ d aargs.reverse bargs.reverse
      | _ => return false
    else return false
  | _, _ => return false

/-- Twin of `lazyDeltaReductionI`. -/
partial def lazyDeltaReduction (μ : CheckMode) (d : Nat) (a b : Expr) : M LazyRes := do
  match ← defeqOffset μ d a b with
  | some v => pure (.verdict v)
  | none =>
  -- the eager flag folds with free variables present
  let fold := μ.eager || (!a.hasFVar && !b.hasFVar)
  match ← (if fold then reduceNat μ d a else pure none) with
  | some a₂ => pure (.verdict (← defeq μ d a₂ b))
  | none =>
  match ← (if fold then reduceNat μ d b else pure none) with
  | some b₂ => pure (.verdict (← defeq μ d a b₂))
  | none =>
  match ← lazyDeltaStep μ d a b with
  | .cont a' b' => lazyDeltaReduction μ d a' b'
  | .eq => pure (.verdict true)
  | .diff => pure (.verdict false)
  | .unknown => pure (.unknown a b)

/-- Twin of `lazyDeltaProjReductionI`. -/
partial def lazyDeltaProjReduction (μ : CheckMode) (d : Nat) (sn : Name) (i : Nat) (a b : Expr) :
    M Bool := do
  match ← lazyDeltaStep μ d a b with
  | .cont a' b' => lazyDeltaProjReduction μ d sn i a' b'
  | .eq => pure true
  | .diff | .unknown =>
    match ← reduceProjCore μ d sn i a with
    | some x =>
      match ← reduceProjCore μ d sn i b with
      | some y => defeq μ d x y
      | none => defeq μ d a b
    | none => defeq μ d a b

/-- Twin of `defeqProjPairI`. -/
partial def defeqProjPair (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match a, b with
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
    if s₁ == s₂ && i₁ == i₂ then lazyDeltaProjReduction μ d s₁ i₁ e₁ e₂ else pure false
  | _, _ => pure false

/-- Twin of `defeqStuckI`. -/
partial def defeqStuck (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  let env := (← read).env
  match a, b with
  | .lit (.strVal s), .app (.const cO []) _ =>
    if cO == stringOfListName && strLitSupported env then
      defeq μ d (strLitToConstructor s) b
    else stuckIrrel μ d a b
  | .app (.const cO []) _, .lit (.strVal s) =>
    if cO == stringOfListName && strLitSupported env then
      defeq μ d a (strLitToConstructor s)
    else stuckIrrel μ d a b
  | .fvar i, .fvar j => if i == j then pure true else stuckIrrel μ d a b
  | .const n us, .const n' us' =>
    if n == n' then
      if ← isEquivListL us us' then pure true else stuckIrrel μ d a b
    else stuckIrrel μ d a b
  | .app .., .app .. =>
    let as₁ := a.getAppArgs
    let as₂ := b.getAppArgs
    if as₁.size == as₂.size then
      if ← defeq μ d a.getAppFn b.getAppFn then
        if ← defEqList μ d as₁ as₂ then pure true else stuckIrrel μ d a b
      else stuckIrrel μ d a b
    else stuckIrrel μ d a b
  | .lam _ ty₁ body₁ _, _ =>
    if ← etaCert μ d ty₁ body₁ b then pure true else stuckIrrel μ d a b
  | _, .lam _ ty₂ body₂ _ =>
    if ← etaCert μ d ty₂ body₂ a then pure true else stuckIrrel μ d a b
  | _, _ => stuckIrrel μ d a b

/-- Twin of `boolTrueShortcutI`. -/
partial def boolTrueShortcut (μ : CheckMode) (d : Nat) (a : Expr) : M Bool := do
  return isBoolTrue (← whnf μ d a)

/-- Twin of `defeqBodyI`. -/
partial def defeqBody (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  if a == b then return true
  -- the eq-true shortcut (E2)
  if isBoolTrue b && (μ.eager || !a.hasFVar) then
    if ← boolTrueShortcut μ d a then return true
  match ← quickDefEq μ d a b with
  | some v => return v
  | none =>
  -- task #333: proof irrelevance before any head normalization
  if ← propIrrel μ d a b then return true
  let a' ← whnfCore μ true d a
  let b' ← whnfCore μ true d b
  match ← quickDefEq μ d a' b' with
  | some v => return v
  | none =>
  match ← lazyDeltaReduction μ d a' b' with
  | .verdict v => return v
  | .unknown a₁ b₁ =>
  if ← defeqProjPair μ d a₁ b₁ then return true
  if !headIsProj a₁ && !headIsProj b₁ then return ← defeqStuck μ d a₁ b₁
  let a₂ ← whnfCore μ false d a₁
  let b₂ ← whnfCore μ false d b₁
  if a₂ == a₁ && b₂ == b₁ then defeqStuck μ d a₁ b₁
  else defeq μ d a₂ b₂

/-- The definitional-equality slot (memoised under the pair). -/
partial def defeq (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  match (← get).defeqC[(a, b)]? with
  | some r => pure r
  | none =>
    let r ← defeqBody μ d a b
    modify fun st =>
      let mp := st.defeqC
      let st := { st with defeqC := {} }
      { st with defeqC := mp.insert (a, b) r }
    pure r

/-- The eager slot (task #353): the same core at `μ.toEager`, on the eager
tower's memos. -/
partial def defeqE (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  withEagerMemos μ (defeq μ.toEager d a b)

end

end Lean.Kernel.InLean
