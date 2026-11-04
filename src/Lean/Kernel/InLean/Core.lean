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

Twin of `ConLeche/Cached/CoreC.lean` on `Lean.Expr`:
`whnfCore` (with the official `cheap_proj` flag), `whnf`, `infer` (full
grade), `inferIO` (official's `infer_only` grade), `defeq` and the eager
tower's `defeqE`, each memoised in `St`, in the official dispatch order
with con-leche's deviations (con-leche's OVERVIEW §3: proof irrelevance before head
normalisation, opaque theorems, the K/structure/`And` rescues, the
verified mode's certificate families).

**One body, every mode.**  Every function takes the mode `μ`; what the
trusted mode omits is exactly what `μ.verifiedChecks` gates (the `certAt`
sites and the λ/η body-type comparisons).  The eager tower is the same
functions at `μ.toEager`, on their own memos (`withEagerMemos`).

**Fuel.**  As in con-leche the core is structural on a fuel that exists for
the proofs' induction; it is effectively unbounded, and the loops iterate in
constant stack.

**What differs from `CoreC` and why** (beyond the data, `Derived.lean`):
* `mdata` is looked through: `whnfCore` steps under it, `infer` infers
  under it (official `whnf_core`/`infer_type_core`); con-leche's `Expr`
  has no `mdata`.
* A free variable's type is the interned one (`St.fvTys`), its scope the
  interned depth (`St.fvDeps`).
* Inference of a constant at the full grade checks the declaration's
  safety against the constant's (official `infer_constant`); con-leche
  checks no unsafe declaration at all (it declines them).
* Substitution is InLean's own (`Lean/Kernel/InLean/ExprOps.lean`), a port of
  con-leche's memoised walks; core's opaque C++ operations are not used.
  Its cutoffs read Lean's cached fields.
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
  let i := ci.type.instLvlParamsI ci.levelParams us
  modify fun s =>
    let mp := s.constTyAt
    let s := { s with constTyAt := {} }
    { s with constTyAt := mp.insert key i }
  return i

def constValAt (n : Name) (lps : List Name) (v : Expr) (us : List Level) : M Expr := do
  if us.isEmpty then return v
  let key := (n, us)
  if let some i := (← get).constValAt[key]? then return i
  let i := v.instLvlParamsI lps us
  modify fun s =>
    let mp := s.constValAt
    let s := { s with constValAt := {} }
    { s with constValAt := mp.insert key i }
  return i

def ruleRhsAt (c : Name) (rx : RecX) (rl : RecRule) (us : List Level) : M Expr := do
  if us.isEmpty then return rl.rhs
  let key := (c, rl.ctor, us)
  if let some i := (← get).ruleRhsAt[key]? then return i
  let i := rl.rhs.instLvlParamsI rx.lps us
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
def proofHead : Expr → Expr
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

namespace Fu

mutual

/-- Twin of the knot's `whnfCore` slot (the two `cheap_proj` modes under
two memos). -/
def whnfCore (fuel : Nat) (μ : CheckMode) (cheap : Bool) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: whnfCore"
  | fuel + 1 => do
      match e with
      | .sort _ | .fvar _ | .forallE .. | .lam .. | .lit _ => return e
      | _ =>
        if cheap then
          memoE (·.whnfCoreCheapC) (fun st mp => { st with whnfCoreCheapC := mp }) e
            fun _ => whnfCoreLoop fuel μ true d e
        else
          memoE (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp }) e
            fun _ => whnfCoreLoop fuel μ false d e
  termination_by structural fuel

/-- Twin of `whnfCoreLoopI`. -/
def whnfCoreLoop (fuel : Nat) (μ : CheckMode) (cheap : Bool) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: whnfCoreLoop"
  | fuel + 1 => do
      match ← whnfCoreStep fuel μ cheap d e with
      | .done v => pure v
      | .cont e' => whnfCoreLoop fuel μ cheap d e'
  termination_by structural fuel

/-- Twin of `whnfCoreStepI`. -/
def whnfCoreStep (fuel : Nat) (μ : CheckMode) (cheap : Bool) (d : Nat) (e : Expr) : M WhnfStep :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: whnfCoreStep"
  | fuel + 1 => do
      match e with
      | .sort _ | .fvar _ | .forallE .. | .lam .. | .const .. | .lit _ => pure (.done e)
      | .mdata _ b => pure (.cont b)
      | .app .. =>
        let h := e.getAppFn
        let args := e.getAppArgs
        let v ← whnfCore fuel μ cheap d h
        whnfApp fuel μ d v args 0
      | .proj sn i pe =>
        let c ← if cheap then whnfCore fuel μ true d pe else whnf fuel μ d pe
        match ← reduceProjCore fuel μ d sn i c with
        | some m' => pure (.cont m')
        | none => pure (.done e)
      | .letE _ _ v b _ => pure (.cont (b.inst1I v))
      | .bvar _ | .mvar _ => throwDeclined "whnf beyond the supported fragment"
  termination_by structural fuel

/-- Twin of `whnfAppI`. -/
def whnfApp (fuel : Nat) (μ : CheckMode) (d : Nat) (v : Expr) (args : Array Expr) (i : Nat) :
    M WhnfStep :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: whnfApp"
  | fuel + 1 => do
      if h : i < args.size then
        let a := args[i]
        match v with
        | .lam _ _ body _ => betaPeel fuel μ d body [a] args (i + 1)
        | _ =>
          let fa := Expr.app v a
          let env := (← read).env
          match ← (if iotaArityOk env fa then iotaRec fuel μ d fa else pure none) with
          | some e'' => pure (.cont (mkAppRange e'' (i + 1) args.size args))
          | none => whnfApp fuel μ d fa args (i + 1)
      else pure (.done v)
  termination_by structural fuel

/-- Twin of `betaPeelI`. -/
def betaPeel (fuel : Nat) (μ : CheckMode) (d : Nat) (t : Expr) (acc : List Expr) (args : Array Expr)
    (i : Nat) : M WhnfStep :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: betaPeel"
  | fuel + 1 => do
      if h : i < args.size then
        match t with
        | .lam _ _ body _ => betaPeel fuel μ d body (args[i] :: acc) args (i + 1)
        | _ =>
          let e' ← instListM t acc
          pure (.cont (mkAppRange e' i args.size args))
      else
        let e' ← instListM t acc
        pure (.cont e')
  termination_by structural fuel

/-- Twin of `whnfBodyI`/`whnfLoopI`/`whnfStepI`, memoised. -/
def whnf (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: whnf"
  | fuel + 1 => do
      match e with
      | .sort _ | .fvar _ | .forallE .. | .lam .. | .lit _ => return e
      | _ => memoE (·.whnfC) (fun st mp => { st with whnfC := mp }) e fun _ => whnfLoop fuel μ d e
  termination_by structural fuel

def whnfLoop (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: whnfLoop"
  | fuel + 1 => do
      let e₁ ← whnfCore fuel μ false d e
      match ← reduceNat fuel μ d e₁ with
      | some e₂ => whnfLoop fuel μ d e₂
      | none =>
        match ← unfoldDefinition e₁ with
        | some e₂ => whnfLoop fuel μ d e₂
        | none => pure e₁
  termination_by structural fuel

/-- Twin of `unfoldDefinitionI`: a theorem never unfolds. -/
def unfoldDefinition (e : Expr) : M (Option Expr) := do
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
def reduceNat (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M (Option Expr) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: reduceNat"
  | fuel + 1 => do
      match e with
      | .app f₁ b =>
        match f₁ with
        | .const c [] =>
          let env := (← read).env
          if c == natSuccName && natLitSupported env then
            let w ← whnf fuel μ d b
            match rawNatLit? w with
            | some n => return some (.lit (.natVal (n + 1)))
            | none => return none
          else return none
        | .app (.const cn []) a =>
          let env := (← read).env
          if (natOpNames.contains cn || natDivModNames.contains cn) && cn != natPredName &&
              natOpStored env cn (← read).uncertifiedNatOps then
            let w₁ ← whnf fuel μ d a
            match rawNatLit? w₁ with
            | some n₁ =>
              let w₂ ← whnf fuel μ d b
              match rawNatLit? w₂ with
              | some n₂ =>
                if let some msg := natOpRefusal cn n₁ n₂ then throwDeclined msg
                return natOpResult cn n₁ n₂
              | none => return none
            | none => return none
          else if natDivModNames.contains cn && natLitSupported env then
            let w₁ ← whnf fuel μ d a
            match rawNatLit? w₁ with
            | some _ =>
              let w₂ ← whnf fuel μ d b
              match rawNatLit? w₂ with
              | some _ => throwDeclined s!"native Nat computation on literals ({cn})"
              | none => return none
            | none => return none
          else return none
        | _ => return none
      | _ => return none
  termination_by structural fuel

/-- Twin of `litToCtorIfNatI`/`litMajorToCtorI`. -/
def litMajorToCtor (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: litMajorToCtor"
  | fuel + 1 => do
      let env := (← read).env
      match e with
      | .lit (.strVal s) =>
        if strLitSupported env then whnf fuel μ d (strLitToConstructor s) else pure e
      | .lit (.natVal n) => if natLitSupported env then pure (natLitToConstructor n) else pure e
      | _ => pure e
  termination_by structural fuel

/-- Twin of `projLitToCtorI`. -/
def projLitToCtor (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: projLitToCtor"
  | fuel + 1 => do
      match e with
      | .lit (.strVal s) =>
        if strLitSupported (← read).env then whnf fuel μ d (strLitToConstructor s) else pure e
      | _ => pure e
  termination_by structural fuel

/-- **The guard levels of a `Prop` structure's projection table** (twin
of `storedGuards`: the fields' sorts by the constructor stage's walk,
then `structProjGuards`), computed on first use. -/
def projGuards (fuel : Nat) (μ : CheckMode) (t : ProjTable) : M (Array Level) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: projGuards"
  | fuel + 1 => do
      if let some g := (← get).guards[t.structName]? then return g
      let mut e := t.ctorType
      let mut fvs : Array Expr := #[]
      for k in [0:t.numParams] do
        match e with
        | .forallE _ dom b _ =>
          let fv ← mkFVar k (dom.instRevI fvs)
          fvs := fvs.push fv
          e := b
        | _ => throwInternal "projection guards: constructor telescope"
      let mut sorts : Array Level := #[]
      for j in [0:t.numFields] do
        match e with
        | .forallE _ dom b _ =>
          let domo := dom.instRevI fvs
          let s ← ensureSort fuel μ (t.numParams + j) (← infer fuel μ (t.numParams + j) domo)
          sorts := sorts.push s
          let fv ← mkFVar (t.numParams + j) domo
          fvs := fvs.push fv
          e := b
        | _ => throwInternal "projection guards: constructor telescope"
      -- `structProjGuards`: field `i`'s sort joined with the sorts of the
      -- earlier fields a later field uses
      let used : Array Bool := (Array.range t.numFields).map fun j =>
        match peelPis (t.numParams + j + 1) t.ctorType with
        | some rest => rest.hasLooseBVarI 0
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
  termination_by structural fuel

/-- Twin of `Env.findProj?`: field `i`'s entry of `T`'s table, its guard
computed only at a `Prop` structure (the only place it is read). -/
def findProj? (fuel : Nat) (μ : CheckMode) (T : Name) (i : Nat) : M (Option ProjEntry) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: findProj?"
  | fuel + 1 => do
      match ← projTableOf T with
      | some t =>
        if i < t.numFields then
          let fs ← if Lvl.isZero t.structSort then
              pure ((← projGuards fuel μ t).getD i .zero)
            else pure .zero
          return some { structName := T, idx := i, levelParams := t.levelParams,
                        numParams := t.numParams, ctor := t.ctor, numFields := t.numFields,
                        body := t.bodies.getD i default, fieldSort := fs,
                        structSort := t.structSort }
        else return none
      | none => return none
  termination_by structural fuel

/-- Twin of `reduceProjCoreI`. -/
def reduceProjCore (fuel : Nat) (μ : CheckMode) (d : Nat) (sn : Name) (i : Nat) (c : Expr) :
    M (Option Expr) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: reduceProjCore"
  | fuel + 1 => do
      let e' ← projLitToCtor fuel μ d c
      match ← findProj? fuel μ sn i with
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
  termination_by structural fuel

/-- Twin of `ProjEntry.fireOk`. -/
def entryFireOk (entry : ProjEntry) (us : List Level) : Bool :=
  !Lvl.isZero entry.structSort ||
    Lvl.isZero (Lvl.subst entry.levelParams us entry.fieldSort)

/-- Twin of `andRescueSlotsOf`. -/
def andRescueSlots (fuel : Nat) (μ : CheckMode) (ctor : Name) (nP : Nat) (ust : List Level) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: andRescueSlots"
  | fuel + 1 => do
      for j in [0:2] do
        match ← findProj? fuel μ andName j with
        | some e =>
          unless e.ctor == ctor && e.numParams == nP && e.numFields == 2 && entryFireOk e ust do
            return false
        | none => return false
      return true
  termination_by structural fuel

/-- Twin of `majorToCtorI`. -/
def majorToCtor (fuel : Nat) (μ : CheckMode) (d : Nat) (rules : Array RecRule) (major : Expr) :
    M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: majorToCtor"
  | fuel + 1 => do
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
                let tmaj ← whnf fuel μ d (← inferIO fuel μ d major)
                match tmaj.getAppFn with
                | .const T' ust =>
                  if T' == T && cvjLps.length == ust.length then
                    let margs := tmaj.getAppArgs
                    if cnP ≤ margs.size then
                      let fab := mkAppN (.const rl.ctor ust) (margs.extract 0 cnP)
                      if (← wscoped d fab) && !fab.hasLooseBVars && (← leafGuard fab major) then
                        -- official `to_cnstr_when_K` fabrication type check (both
                        -- modes); its proof irrelevance is a certificate family
                        let tfab ← inferIO fuel μ d fab
                        if ← defeq fuel μ d tmaj tfab then
                          if ← certAt μ (proofIrrel fuel μ d fab major) then return fab
                          else return major
                        else return major
                      else return major
                    else return major
                  else return major
                | _ => return major
              else if rl.eta then
                let tmaj ← whnf fuel μ d (← inferIO fuel μ d major)
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
                    -- no certificate on the fabricated spine
                    if (← wscoped d fab) && !fab.hasLooseBVars && (← leafGuard fab major) then
                      return fab
                    else return major
                  else return major
                | _ => return major
              else if T == andName then
                -- the `And`-only rescue
                let tmaj ← whnf fuel μ d (← inferIO fuel μ d major)
                match tmaj.getAppFn with
                | .const T' ust =>
                  let margs := tmaj.getAppArgs
                  if T' == T && margs.size == cnP && cvjLps.length == ust.length &&
                      (← andRescueSlots fuel μ rl.ctor cnP ust) then
                    let projs := #[Expr.proj T 0 major, Expr.proj T 1 major]
                    let fab := mkAppN (.const rl.ctor ust) (margs ++ projs)
                    if (← wscoped d fab) && !fab.hasLooseBVars && (← leafGuard fab major) then
                      let tfab ← inferIO fuel μ d fab
                      if ← defeq fuel μ d tmaj tfab then
                        if ← certAt μ (proofIrrel fuel μ d fab major) then return fab
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
  termination_by structural fuel

/-- Twin of `prepareMajorI`. -/
def prepareMajor (fuel : Nat) (μ : CheckMode) (d : Nat) (rules : Array RecRule) (major : Expr) :
    M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: prepareMajor"
  | fuel + 1 => do
      let env := (← read).env
      if recRuleK rules then
        let majorK ← majorToCtor fuel μ d rules major
        if isCtorApp env majorK then litMajorToCtor fuel μ d majorK else pure majorK
      else
        let majorE ← match major with
          | .lit (.strVal _) => pure major
          | _ => majorToCtor fuel μ d rules major
        if isCtorApp env majorE then pure majorE
        else
          let major₀ ← whnf fuel μ d majorE
          let major₁ ← litMajorToCtor fuel μ d major₀
          majorToCtor fuel μ d rules major₁
  termination_by structural fuel

/-- Twin of `defEqListI`. -/
def defEqList (fuel : Nat) (μ : CheckMode) (d : Nat) (as bs : Array Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defEqList"
  | fuel + 1 => do
      if as.size != bs.size then return false
      for i in [0:as.size] do
        unless ← defeq fuel μ d (as.getD i default) (bs.getD i default) do return false
      return true
  termination_by structural fuel

/-- Twin of `iotaCertsFullIAux`. -/
def iotaCertsFull (fuel : Nat) (μ : CheckMode) (d : Nat) (ty : Expr) (acc : List Expr)
    (args : Array Expr) (i : Nat) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: iotaCertsFull"
  | fuel + 1 => do
      if h : i < args.size then
        let arg := args[i]
        match ty with
        | .forallE _ dom body _ =>
          let dom' ← instListM dom acc
          let ta ← infer fuel μ d arg
          if ← defeq fuel μ d ta dom' then iotaCertsFull fuel μ d body (arg :: acc) args (i + 1)
          else return false
        | .bvar _ =>
          if acc.isEmpty then return false
          let ty' ← instListM ty acc
          iotaCertsFull fuel μ d ty' [] args i
        | _ => return false
      else return true
  termination_by structural fuel

/-- Twin of `iotaIndexOkI`. -/
def iotaIndexOk (fuel : Nat) (μ : CheckMode) (d : Nat) (mI rP cnP : Nat) (tyCtor : Expr)
    (margs idx : Array Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: iotaIndexOk"
  | fuel + 1 => do
      if mI == rP then return true
      match piResidual tyCtor margs with
      | some residual => defEqList fuel μ d (residual.getAppArgs.extract cnP) idx
      | none => return false
  termination_by structural fuel

/-- Twin of `iotaRecI`. -/
def iotaRec (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M (Option Expr) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: iotaRec"
  | fuel + 1 => do
      match e.getAppFn with
      | .const c us =>
        match ← recOf c with
        | some rx =>
          let args := e.getAppArgs
          let mI := rx.majorIdx
          let rP := rx.rulePrefix
          if args.size == mI + 1 && us.length == rx.lps.length &&
              (peelPis (mI + 1) rx.type).isSome then
            let major ← prepareMajor fuel μ d rx.rules (args.getD mI (.bvar 0))
            match major.getAppFn with
            | .const cj usj =>
              match ctorView? (← read).env cj with
              | some (cvjLps, cvjType, _, _) =>
                match rx.rules.find? (·.ctor == cj) with
                | some rl =>
                  let margs := major.getAppArgs
                  if margs.size == rl.ctorParams + rl.nfields then
                    -- the case-3 certificate family
                    if ← certAt μ (do
                        let cmpLvls : List Level := match rl.fire with
                          | .nested lvls _ => lvls.map (Lvl.subst rx.lps us)
                          | .plain => cvjLps.map fun p => Lvl.subst rx.lps us (.param p)
                        if !rl.k && !(← iotaCtorNeverProp cvjType cmpLvls) then
                          if ← isEquivListL usj cmpLvls then
                            let cmpArgs : Array Expr := match rl.fire with
                              | .nested _ pins =>
                                pins.map fun p =>
                                  (p.instLvlParamsI rx.lps us).instRevI (args.extract 0 rP)
                              | .plain => args.extract 0 rl.ctorParams
                            if ← defEqList fuel μ d (margs.extract 0 rl.ctorParams) cmpArgs then
                              let some ci := (← read).env.find? cj
                                | return false
                              let tyCtor ← constTyAt ci usj
                              if ← iotaCertsFull fuel μ d tyCtor [] margs 0 then
                                iotaIndexOk fuel μ d mI rP rl.ctorParams tyCtor margs
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
  termination_by structural fuel

/-- Twin of `ensureSortI`. -/
def ensureSort (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M Level :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: ensureSort"
  | fuel + 1 => do
      match ← whnf fuel μ d e with
      | .sort u => pure u
      | _ => throwInvalid "expected a sort"
  termination_by structural fuel

/-- The full-grade inference slot (memoised). -/
def infer (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: infer"
  | fuel + 1 =>
      memoE (·.inferC) (fun st mp => { st with inferC := mp }) e fun _ => inferBody fuel μ false d e
  termination_by structural fuel

/-- The infer-only slot (memoised apart). -/
def inferIO (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: inferIO"
  | fuel + 1 =>
      memoE (·.inferIOC) (fun st mp => { st with inferIOC := mp }) e fun _ => inferBody fuel μ true d e
  termination_by structural fuel

@[inline] def inferG (fuel : Nat) (μ : CheckMode) (io : Bool) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: inferG"
  | fuel + 1 =>
      if io then inferIO fuel μ d e else infer fuel μ d e
  termination_by structural fuel

/-- Twin of `inferBodyI` (`io = false`) and `inferBodyIOI` (`io = true`). -/
def inferBody (fuel : Nat) (μ : CheckMode) (io : Bool) (d : Nat) (e : Expr) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: inferBody"
  | fuel + 1 => do
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
      | .mdata _ b => inferG fuel μ io d b
      | .forallE n ty body bi =>
        if io then
          let u ← ensureSort fuel μ d (← inferIO fuel μ d ty)
          let fv ← mkFVar d ty
          let v ← ensureSort fuel μ (d + 1) (← inferIO fuel μ (d + 1) (body.inst1I fv))
          let _ := (n, bi)
          pure (.sort (.imax u v))
        else inferPis fuel μ d e 0 #[] []
      | .lam n ty body bi =>
        if io then
          let fv ← mkFVar d ty
          let bt ← inferIO fuel μ (d + 1) (body.inst1I fv)
          pure (.forallE n ty (← abstractChecked bt #[fv]) bi)
        else inferLams fuel μ d e 0 #[] []
      | .app .. =>
        let h := e.getAppFn
        let args := e.getAppArgs
        if io then
          let tf ← inferIO fuel μ d h
          inferSpineIO fuel μ d tf #[] args 0
        else
          let tf ← infer fuel μ d h
          inferSpine fuel μ d tf #[] args 0
      | .proj sn i pe =>
        let te ← whnf fuel μ d (← inferG fuel μ io d pe)
        match te.getAppFn with
        | .const T us =>
          match ← findProj? fuel μ T i with
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
        if io then inferIO fuel μ d (b.inst1I v)
        else
          let _ ← ensureSort fuel μ d (← infer fuel μ d ty)
          let tv ← infer fuel μ d v
          unless ← defeq fuel μ d tv ty do throwInvalid "let value type mismatch"
          infer fuel μ d (b.inst1I v)
      | .bvar _ => throwDeclined "inferType beyond the supported fragment"
      | .mvar _ => throwInvalid "unexpected metavariable"
  termination_by structural fuel

/-- Twin of `inferPisI` (the ∀-telescope loop): peel, check each opened
domain is a type, infer the bulk-opened leaf's sort, fold `imax`. -/
def inferPis (fuel : Nat) (μ : CheckMode) (d : Nat) (t : Expr) (k : Nat) (fvs : Array Expr)
    (stk : List Level) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: inferPis"
  | fuel + 1 => do
      match t with
      | .forallE _ ty body _ =>
        let tyo := ty.instRevI fvs
        match ← whnf fuel μ (d + k) (← infer fuel μ (d + k) tyo) with
        | .sort u =>
          let fv ← mkFVar (d + k) tyo
          inferPis fuel μ d body (k + 1) (fvs.push fv) (u :: stk)
        | _ => throwInvalid "expected a sort"
      | _ =>
        let ob := t.instRevI fvs
        match ← whnf fuel μ (d + k) (← infer fuel μ (d + k) ob) with
        | .sort v => pure (.sort (stk.foldl (fun acc u => .imax u acc) v))
        | _ => throwInvalid "expected a sort"
  termination_by structural fuel

/-- Twin of `inferLamsI` (the λ-telescope loop): peel, check each opened
domain is a type, infer the bulk-opened leaf, rebuild with
`abstractRange`. -/
def inferLams (fuel : Nat) (μ : CheckMode) (d : Nat) (t : Expr) (k : Nat) (fvs : Array Expr)
    (stk : List (Name × BinderInfo × Expr)) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: inferLams"
  | fuel + 1 => do
      match t with
      | .lam n ty body bi =>
        let tyo := ty.instRevI fvs
        match ← whnf fuel μ (d + k) (← infer fuel μ (d + k) tyo) with
        | .sort _ =>
          let fv ← mkFVar (d + k) tyo
          inferLams fuel μ d body (k + 1) (fvs.push fv) ((n, bi, tyo) :: stk)
        | _ => throwInvalid "expected a sort"
      | _ =>
        let ob := t.instRevI fvs
        let bt ← infer fuel μ (d + k) ob
        let mut cur ← abstractRangeChecked bt k fvs
        let mut j := k
        for (n, bi, tyo) in stk do
          j := j - 1
          cur := .forallE n (← abstractRangeChecked tyo j fvs) cur bi
        pure cur
  termination_by structural fuel

/-- Twin of `defeqArgI`. -/
@[inline] def defeqArg (fuel : Nat) (μ : CheckMode) (d : Nat) (a ta ty : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqArg"
  | fuel + 1 =>
      if isEagerReduce a then defeqE fuel μ d ta ty else defeq fuel μ d ta ty
  termination_by structural fuel

/-- Twin of `inferSpineI`. -/
def inferSpine (fuel : Nat) (μ : CheckMode) (d : Nat) (ty : Expr) (acc : Array Expr)
    (args : Array Expr) (i : Nat) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: inferSpine"
  | fuel + 1 => do
      if h : i < args.size then
        let a := args[i]
        match ty with
        | .forallE _ dom body _ =>
          let dom' := dom.instRevI acc
          let ta ← infer fuel μ d a
          unless ← defeqArg fuel μ d a ta dom' do throwInvalid (appMismatchMsg a ta dom')
          inferSpine fuel μ d body (acc.push a) args (i + 1)
        | _ =>
          match ← whnf fuel μ d (ty.instRevI acc) with
          | .forallE _ dom body _ =>
            let ta ← infer fuel μ d a
            unless ← defeqArg fuel μ d a ta dom do throwInvalid (appMismatchMsg a ta dom)
            inferSpine fuel μ d body #[a] args (i + 1)
          | _ => throwInvalid "function expected"
      else pure (ty.instRevI acc)
  termination_by structural fuel

/-- Twin of `inferSpineIOI`. -/
def inferSpineIO (fuel : Nat) (μ : CheckMode) (d : Nat) (ty : Expr) (acc : Array Expr)
    (args : Array Expr) (i : Nat) : M Expr :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: inferSpineIO"
  | fuel + 1 => do
      if h : i < args.size then
        let a := args[i]
        match ty with
        | .forallE _ _ body _ => inferSpineIO fuel μ d body (acc.push a) args (i + 1)
        | _ =>
          match ← whnf fuel μ d (ty.instRevI acc) with
          | .forallE _ _ body _ => inferSpineIO fuel μ d body #[a] args (i + 1)
          | _ => throwInvalid "function expected"
      else pure (ty.instRevI acc)

-- Definitional equality
  termination_by structural fuel

/-- Twin of `proofIrrelI`. -/
def proofIrrel (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: proofIrrel"
  | fuel + 1 => do
      match ← whnf fuel μ d (← inferIO fuel μ d (← inferIO fuel μ d a)) with
      | .sort uT =>
        let okA ← isEquivL uT .zero
        match ← whnf fuel μ d (← inferIO fuel μ d (← inferIO fuel μ d b)) with
        | .sort vT =>
          let okB ← isEquivL vT .zero
          pure (okA && okB)
        | _ => pure false
      | _ => pure false
  termination_by structural fuel

/-- Twin of `propIrrelI`: the head-symbol readers first. -/
def propIrrel (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: propIrrel"
  | fuel + 1 => do
      if (← notProofFast a) || (← notProofFast b) then return false
      if (← isProofFast a) && (← isProofFast b) then return true
      proofIrrel fuel μ d a b
  termination_by structural fuel

/-- Twin of `structEtaCertWithI`. -/
def structEtaCertWith (fuel : Nat) (μ : CheckMode) (d : Nat) (a b wtb : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: structEtaCertWith"
  | fuel + 1 => do
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
                    if ← defEqList fuel μ d (aargs.extract 0 caps.etaParams) targs then
                      let projs := (Array.range caps.etaFields).map fun j => Expr.proj T j b
                      defEqList fuel μ d (aargs.extract caps.etaParams) projs
                    else return false
                  else return false
                else return false
              | _, _ => return false
            | _ => return false
          else return false
        | _ => return false
      | _ => return false
  termination_by structural fuel

/-- Twin of `structEtaCertI`. -/
def structEtaCert (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: structEtaCert"
  | fuel + 1 => do
      if etaCtorShape (← read).env a then
        let wtb ← whnf fuel μ d (← inferIO fuel μ d b)
        structEtaCertWith fuel μ d a b wtb
      else return false
  termination_by structural fuel

/-- Twin of `structUnitCertI`. -/
def structUnitCert (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: structUnitCert"
  | fuel + 1 => do
      let wta ← whnf fuel μ d (← inferIO fuel μ d a)
      match wta.getAppFn with
      | .const T us' =>
        match (← read).env.find? T, ← capsOf T with
        | some (.inductInfo cvT), some caps =>
          if caps.unitlike && !reservedBasisNames.contains T &&
              wta.getAppNumArgs == caps.unitParams && us'.length == cvT.levelParams.length then
            let wtb ← whnf fuel μ d (← inferIO fuel μ d b)
            if wtb.isForall then return false
            defeq fuel μ d wta wtb
          else return false
        | _, _ => return false
      | _ => return false
  termination_by structural fuel

/-- Twin of `etaCertI`. -/
def etaCert (fuel : Nat) (μ : CheckMode) (d : Nat) (ty₁ body₁ b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: etaCert"
  | fuel + 1 => do
      if !ioNeutral b then return false
      match ← whnf fuel μ d (← inferIO fuel μ d b) with
      | .forallE _ ty₂ cod₂ _ =>
        if ← defeq fuel μ d ty₂ ty₁ then
          let fv ← mkFVar d ty₁
          let b₁ := body₁.inst1I fv
          unless ← defeq fuel μ (d + 1) b₁ (.app b fv) do return false
          if μ.verifiedChecks then
            let t₁ ← infer fuel μ (d + 1) b₁
            unless ← defeq fuel μ (d + 1) t₁ (cod₂.inst1I fv) do return false
          return true
        else return false
      | _ => return false
  termination_by structural fuel

/-- Twin of `stuckIrrelI`. -/
def stuckIrrel (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: stuckIrrel"
  | fuel + 1 => do
      if ← structEtaCert fuel μ d a b then return true
      if ← structEtaCert fuel μ d b a then return true
      if ← structUnitCert fuel μ d a b then return true
      proofIrrel fuel μ d a b
  termination_by structural fuel

/-- Twin of `defeqLamsI` (the λ/λ telescope; the body types compared at
the innermost level in the verified modes). -/
def defeqLams (fuel : Nat) (μ : CheckMode) (d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqLams"
  | fuel + 1 => do
      unless ← defeq fuel μ d ty₁ ty₂ do return false
      let fv ← mkFVar d ty₂
      let b₁ := body₁.inst1I fv
      let b₂ := body₂.inst1I fv
      match b₁, b₂ with
      | .lam _ ty₁' body₁' _, .lam _ ty₂' body₂' _ =>
        if b₁ == b₂ then return true
        defeqLams fuel μ (d + 1) ty₁' body₁' ty₂' body₂'
      | _, _ =>
        unless ← defeq fuel μ (d + 1) b₁ b₂ do return false
        if μ.verifiedChecks then
          let t₁ ← infer fuel μ (d + 1) b₁
          let t₂ ← infer fuel μ (d + 1) b₂
          unless ← defeq fuel μ (d + 1) t₁ t₂ do return false
        return true
  termination_by structural fuel

/-- Twin of `quickDefEqI`. -/
def quickDefEq (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M (Option Bool) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: quickDefEq"
  | fuel + 1 => do
      if a == b then return some true
      match a, b with
      | .sort u, .sort v => return some (← isEquivL u v)
      | .lit l₁, .lit l₂ => return some (l₁ == l₂)
      | .forallE _ ty₁ body₁ _, .forallE _ ty₂ body₂ _ =>
        unless ← defeq fuel μ d ty₁ ty₂ do return some false
        let fv ← mkFVar d ty₂
        unless ← defeq fuel μ (d + 1) (body₁.inst1I fv) (body₂.inst1I fv) do
          return some false
        return some true
      | .lam _ ty₁ body₁ _, .lam _ ty₂ body₂ _ => return some (← defeqLams fuel μ d ty₁ body₁ ty₂ body₂)
      | _, _ => return none
  termination_by structural fuel

/-- Twin of `defeqOffsetI`. -/
def defeqOffset (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M (Option Bool) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqOffset"
  | fuel + 1 => do
      if isNatZero a && isNatZero b then return some true
      if a.isLit && b.isLit then return none
      match natPred? a, natPred? b with
      | some x, some y => return some (← defeq fuel μ d x y)
      | _, _ => return none
  termination_by structural fuel

/-- Twin of `tryUnfoldProjAppI`. -/
def tryUnfoldProjApp (fuel : Nat) (μ : CheckMode) (d : Nat) (e : Expr) : M (Option Expr) :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: tryUnfoldProjApp"
  | fuel + 1 => do
      if headIsProj e then
        let e' ← whnfCore fuel μ false d e
        if e' == e then return none else return some e'
      else return none
  termination_by structural fuel

/-- Twin of `deltaQuickI`. -/
def deltaQuick (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M DeltaStep :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: deltaQuick"
  | fuel + 1 => do
      match ← quickDefEq fuel μ d a b with
      | some true => pure .eq
      | some false => pure .diff
      | none => pure (.cont a b)
  termination_by structural fuel

/-- Twin of `lazyDeltaStepI`. -/
def lazyDeltaStep (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M DeltaStep :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: lazyDeltaStep"
  | fuel + 1 => do
      let env := (← read).env
      match unfoldableHead env a, unfoldableHead env b with
      | false, false => pure .unknown
      | true, false =>
        match ← tryUnfoldProjApp fuel μ d b with
        | some b₂ => deltaQuick fuel μ d a b₂
        | none =>
          match ← unfoldDefinition a with
          | some a₂ => deltaQuick fuel μ d (← whnfCore fuel μ true d a₂) b
          | none => pure .unknown
      | false, true =>
        match ← tryUnfoldProjApp fuel μ d a with
        | some a₂ => deltaQuick fuel μ d a₂ b
        | none =>
          match ← unfoldDefinition b with
          | some b₂ => deltaQuick fuel μ d a (← whnfCore fuel μ true d b₂)
          | none => pure .unknown
      | true, true =>
        let ha := headHint env a
        let hb := headHint env b
        if hintLt hb ha then
          match ← unfoldDefinition a with
          | some a₂ => deltaQuick fuel μ d (← whnfCore fuel μ true d a₂) b
          | none => pure .unknown
        else if hintLt ha hb then
          match ← unfoldDefinition b with
          | some b₂ => deltaQuick fuel μ d a (← whnfCore fuel μ true d b₂)
          | none => pure .unknown
        else if ← (if hintSameRegular ha hb && sameConstHeads a b then defeqSpine fuel μ d a b
            else pure false) then pure .eq
        else
          match ← unfoldDefinition a, ← unfoldDefinition b with
          | some a₂, some b₂ =>
            let a₃ ← whnfCore fuel μ true d a₂
            let b₃ ← whnfCore fuel μ true d b₂
            deltaQuick fuel μ d a₃ b₃
          | _, _ => pure .unknown
  termination_by structural fuel

/-- Twin of `defeqSpineI` (arguments last to first, official
`is_def_eq_args`). -/
def defeqSpine (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqSpine"
  | fuel + 1 => do
      match a.getAppFn, b.getAppFn with
      | .const n us, .const n' us' =>
        let aargs := a.getAppArgs
        let bargs := b.getAppArgs
        if n == n' && aargs.size == bargs.size then
          match ← isEquivListLM us us' with
          | some true => defEqList fuel μ d aargs.reverse bargs.reverse
          | _ => return false
        else return false
      | _, _ => return false
  termination_by structural fuel

/-- Twin of `lazyDeltaReductionI`. -/
def lazyDeltaReduction (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M LazyRes :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: lazyDeltaReduction"
  | fuel + 1 => do
      match ← defeqOffset fuel μ d a b with
      | some v => pure (.verdict v)
      | none =>
      -- the eager flag folds with free variables present
      let fold := μ.eager || (!a.hasFVar && !b.hasFVar)
      match ← (if fold then reduceNat fuel μ d a else pure none) with
      | some a₂ => pure (.verdict (← defeq fuel μ d a₂ b))
      | none =>
      match ← (if fold then reduceNat fuel μ d b else pure none) with
      | some b₂ => pure (.verdict (← defeq fuel μ d a b₂))
      | none =>
      match ← lazyDeltaStep fuel μ d a b with
      | .cont a' b' => lazyDeltaReduction fuel μ d a' b'
      | .eq => pure (.verdict true)
      | .diff => pure (.verdict false)
      | .unknown => pure (.unknown a b)
  termination_by structural fuel

/-- Twin of `lazyDeltaProjReductionI`. -/
def lazyDeltaProjReduction (fuel : Nat) (μ : CheckMode) (d : Nat) (sn : Name) (i : Nat) (a b : Expr) :
    M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: lazyDeltaProjReduction"
  | fuel + 1 => do
      match ← lazyDeltaStep fuel μ d a b with
      | .cont a' b' => lazyDeltaProjReduction fuel μ d sn i a' b'
      | .eq => pure true
      | .diff | .unknown =>
        match ← reduceProjCore fuel μ d sn i a with
        | some x =>
          match ← reduceProjCore fuel μ d sn i b with
          | some y => defeq fuel μ d x y
          | none => defeq fuel μ d a b
        | none => defeq fuel μ d a b
  termination_by structural fuel

/-- Twin of `defeqProjPairI`. -/
def defeqProjPair (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqProjPair"
  | fuel + 1 =>
      match a, b with
      | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
        if s₁ == s₂ && i₁ == i₂ then lazyDeltaProjReduction fuel μ d s₁ i₁ e₁ e₂ else pure false
      | _, _ => pure false
  termination_by structural fuel

/-- Twin of `defeqStuckI`. -/
def defeqStuck (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqStuck"
  | fuel + 1 => do
      let env := (← read).env
      match a, b with
      | .lit (.strVal s), .app (.const cO []) _ =>
        if cO == stringOfListName && strLitSupported env then
          defeq fuel μ d (strLitToConstructor s) b
        else stuckIrrel fuel μ d a b
      | .app (.const cO []) _, .lit (.strVal s) =>
        if cO == stringOfListName && strLitSupported env then
          defeq fuel μ d a (strLitToConstructor s)
        else stuckIrrel fuel μ d a b
      | .fvar i, .fvar j =>
        -- con-leche compares two variables by LEVEL (`.fvar i _, .fvar j _ => i == j`): a
        -- variable's reading ignores its annotation; the interned ids include it
        if i == j then pure true else
        match ← fvarInfo? i, ← fvarInfo? j with
        | some (_, di), some (_, dj) => if di == dj then pure true else stuckIrrel fuel μ d a b
        | _, _ => stuckIrrel fuel μ d a b
      | .const n us, .const n' us' =>
        if n == n' then
          if ← isEquivListL us us' then pure true else stuckIrrel fuel μ d a b
        else stuckIrrel fuel μ d a b
      | .app .., .app .. =>
        let as₁ := a.getAppArgs
        let as₂ := b.getAppArgs
        if as₁.size == as₂.size then
          if ← defeq fuel μ d a.getAppFn b.getAppFn then
            if ← defEqList fuel μ d as₁ as₂ then pure true else stuckIrrel fuel μ d a b
          else stuckIrrel fuel μ d a b
        else stuckIrrel fuel μ d a b
      | .lam _ ty₁ body₁ _, _ =>
        if ← etaCert fuel μ d ty₁ body₁ b then pure true else stuckIrrel fuel μ d a b
      | _, .lam _ ty₂ body₂ _ =>
        if ← etaCert fuel μ d ty₂ body₂ a then pure true else stuckIrrel fuel μ d a b
      | _, _ => stuckIrrel fuel μ d a b
  termination_by structural fuel

/-- Twin of `boolTrueShortcutI`. -/
def boolTrueShortcut (fuel : Nat) (μ : CheckMode) (d : Nat) (a : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: boolTrueShortcut"
  | fuel + 1 => do
      return isBoolTrue (← whnf fuel μ d a)
  termination_by structural fuel

/-- Twin of `defeqBodyI`. -/
def defeqBody (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqBody"
  | fuel + 1 => do
      if a == b then return true
      -- the eq-true shortcut (E2)
      if isBoolTrue b && (μ.eager || !a.hasFVar) then
        if ← boolTrueShortcut fuel μ d a then return true
      match ← quickDefEq fuel μ d a b with
      | some v => return v
      | none =>
      -- proof irrelevance before any head normalization
      if ← propIrrel fuel μ d a b then return true
      let a' ← whnfCore fuel μ true d a
      let b' ← whnfCore fuel μ true d b
      match ← quickDefEq fuel μ d a' b' with
      | some v => return v
      | none =>
      match ← lazyDeltaReduction fuel μ d a' b' with
      | .verdict v => return v
      | .unknown a₁ b₁ =>
      if ← defeqProjPair fuel μ d a₁ b₁ then return true
      if !headIsProj a₁ && !headIsProj b₁ then return ← defeqStuck fuel μ d a₁ b₁
      let a₂ ← whnfCore fuel μ false d a₁
      let b₂ ← whnfCore fuel μ false d b₁
      if a₂ == a₁ && b₂ == b₁ then defeqStuck fuel μ d a₁ b₁
      else defeq fuel μ d a₂ b₂
  termination_by structural fuel

/-- The definitional-equality slot (memoised under the pair). -/
def defeq (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeq"
  | fuel + 1 => do
      match (← get).defeqC[(a, b)]? with
      | some r => pure r
      | none =>
        let r ← defeqBody fuel μ d a b
        modify fun st =>
          let mp := st.defeqC
          let st := { st with defeqC := {} }
          { st with defeqC := mp.insert (a, b) r }
        pure r
  termination_by structural fuel

/-- The eager slot: the same core at `μ.toEager`, on the eager
tower's memos. -/
def defeqE (fuel : Nat) (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool :=
  match fuel with
  | 0 => throwInternal "fuel exhausted: defeqE"
  | fuel + 1 =>
      withEagerMemos μ (defeq fuel μ.toEager d a b)
  termination_by structural fuel

end

end Fu

/-- Twin of `checkFuel` (2^62, hoisted: a literal above 2^32 would be parsed at
every evaluation). -/
@[noinline] def checkFuel : Nat := 4611686018427387904

/-! ## The entry points at `checkFuel` (twin of `coreKnotI mode fe checkFuel`) -/

def whnfCore (μ : CheckMode) (cheap : Bool) (d : Nat) (e : Expr) : M Expr :=
  Fu.whnfCore checkFuel μ cheap d e
def whnf (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := Fu.whnf checkFuel μ d e
def infer (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := Fu.infer checkFuel μ d e
def inferIO (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := Fu.inferIO checkFuel μ d e
def defeq (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := Fu.defeq checkFuel μ d a b
def defeqE (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := Fu.defeqE checkFuel μ d a b
def ensureSort (μ : CheckMode) (d : Nat) (e : Expr) : M Level := Fu.ensureSort checkFuel μ d e

end Lean.Kernel.InLean
