/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.CoreDefs
public import Lean.Kernel.InLean.Pins

/-!
# InLean: the checker core

Twin of `ConLeche.Cached.CoreC` on `Lean.Expr`, function by function
and in its shape: the bodies are templates over the mode and the knot of
closures at the end (`coreKnotI`) ties them at a fuel; `whnfCore`, `whnf`,
`infer`, `inferIO` and `defeq` are each memoised in `CState`.  Each
function's docstring names the con-leche function it is the twin of.

What differs, and why:
* A free variable is an interned id (`Lean.Kernel.InLean.StateC`): building one
  is `mkFVarM`, its type is read from the state, and two are compared by
  depth, as con-leche compares its levels (`defeqStuckI`).
* `mdata` is looked through (`whnfCoreStepI`, `inferBodyI`, the readers),
  as the official kernel does; a metavariable is not supported.
* What con-leche's install stores is read off Lean's entry at use
  (`Lean.Kernel.InLean.FEnv`): the capabilities, a recursor's counts and its
  rules' firing mode (only in ι's case-3 certificate), a constructor's
  counts, a projection's table entry and, in inference, its body.
* Inference of a constant checks the declaration's safety against the
  constant's (official `infer_constant`); con-leche checks safe
  declarations only.
* A `Nat` literal computation the official kernel refuses (`natOpRefusal`,
  `natResultRefused`) is an error here too, and so is the inference of a
  literal past the size bound (`Limits.natMaxBytes`).
* The official kernel's resource limits (`Limits`): the knot's fuel is the
  recursion bound, and every body runs behind the poll (`pollC`).
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

/-- Twin of `whnfCoreLoopFuel`. -/
@[irreducible, noinline] def whnfCoreLoopFuel : Nat := 4611686018427387904  -- 2^62
/-- Twin of `whnfLoopFuel`. -/
@[irreducible, noinline] def whnfLoopFuel : Nat := 4611686018427387904  -- 2^62
/-- Twin of `lamsFuel`. -/
@[irreducible, noinline] def lamsFuel : Nat := 4611686018427387904  -- 2^62
/-- Twin of `defeqLoopFuel`. -/
@[irreducible, noinline] def defeqLoopFuel : Nat := 4611686018427387904  -- 2^62
/-- Twin of `checkFuel`. -/
@[irreducible, noinline] def checkFuel : Nat := 4611686018427387904  -- 2^62

/-! ## The core record and its helper twins -/

/-- Twin of `CoreFnsI`. -/
structure CoreFnsI where
  whnfCore : Bool → Nat → Expr → CheckCM Expr
  whnf : Nat → Expr → CheckCM Expr
  infer : Nat → Expr → CheckCM Expr
  defeq : Nat → Expr → Expr → CheckCM Bool
  defeqE : Nat → Expr → Expr → CheckCM Bool
  inferIO : Nat → Expr → CheckCM Expr

/-- Twin of `CoreFnsI.ioView`. -/
def CoreFnsI.ioView (r : CoreFnsI) : CoreFnsI :=
  { r with infer := r.inferIO }

/-- The application spine's arguments as a list (twin of `getAppArgsC`). -/
def appArgs (e : Expr) : List Expr := go e []
where
  go : Expr → List Expr → List Expr
    | .app f a, acc => go f (a :: acc)
    | .mdata _ e, acc => go e acc
    | _, acc => acc

/-! ### The stored-constant caches -/

/-- The quotient eliminator's rule at the record's level names (the pins
`quotLiftA`/`quotIndA`, renamed as `quotAt` renames them). -/
def quotRuleRhs (q : QuotVal) : Expr :=
  if q.kind == .lift then
    quotLiftRule.instLvlParamsI [BasisDSL.uN, BasisDSL.vN] (q.levelParams.map .param)
  else quotIndRule.instLvlParamsI [BasisDSL.uN] (q.levelParams.map .param)

/-- The recursor at `n`, and whether it is a quotient eliminator. -/
def FEnv.recAt? (fe : FEnv) (n : Name) : Option (RecursorVal × Bool) :=
  match fe.find? n with
  | some (.recInfo rv) => some (rv, false)
  | some (.quotInfo q) => (quotRecVal q (quotRuleRhs q)).map (·, true)
  | _ => none

/-- Twin of `constTyAtM`. -/
def constTyAtM (fe : FEnv) (n : Name) (us : List Level) : CheckCM Expr := do
  let hit? ← modifyGet fun s => (s.constTyAt[(n, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.find? n with
    | some ci =>
      let i ← instLevelParamsM ci.levelParams us ci.type
      modify fun s =>
        let mp := s.constTyAt
        let s := { s with constTyAt := ∅ }
        { s with constTyAt := mp.insert (n, us) i }
      pure i
    | none => throw (.internal "constTyAtM: unknown constant")

/-- Twin of `constValAtM`. -/
def constValAtM (fe : FEnv) (n : Name) (us : List Level) : CheckCM Expr := do
  let hit? ← modifyGet fun s => (s.constValAt[(n, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.defnView? n with
    | some (cv, v, _) =>
      let i ← instLevelParamsM cv.levelParams us v
      modify fun s =>
        let mp := s.constValAt
        let s := { s with constValAt := ∅ }
        { s with constValAt := mp.insert (n, us) i }
      pure i
    | none => throw (.internal "constValAtM: not a stored definition")

/-- Twin of `ruleRhsAtM`. -/
def ruleRhsAtM (fe : FEnv) (c j : Name) (us : List Level) : CheckCM Expr := do
  let hit? ← modifyGet fun s => (s.ruleRhsAt[(c, j, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.recAt? c with
    | some (rv, _) =>
      match rv.rules.find? (fun r' => r'.ctor == j) with
      | some rl =>
        let i ← instLevelParamsM rv.levelParams us rl.rhs
        modify fun s =>
          let mp := s.ruleRhsAt
          let s := { s with ruleRhsAt := ∅ }
          { s with ruleRhsAt := mp.insert (c, j, us) i }
        pure i
      | none => throw (.internal "ruleRhsAtM: no rule for constructor")
    | none => throw (.internal "ruleRhsAtM: not a stored recursor")

/-! ### Mode-free bodies -/

/-- **The limits' poll** (`Limits.poll`) at an event, before `x`: a limit
it answers is the error. -/
@[inline] def pollC (fe : FEnv) (ev : Event) (x : CheckCM α) : CheckCM α :=
  match fe.limits.poll with
  | none => x
  | some p =>
    match p ev with
    | some l => throw (.limit l)
    | none => x

/-- Twin of `unfoldDefinitionI`: a theorem never unfolds; the unfolding is
reported to the poll (`Event.unfold`). -/
def unfoldDefinitionI (fe : FEnv) (e : Expr) : CheckCM (Option Expr) := do
  match e.getAppFnT with
  | .const n us => do
    match fe.defnView? n with
    | some (cv, _, _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n us
        let r ← mkAppNM v (appArgs e)
        pollC fe (.unfold n) (pure (some r))
      else pure none
    | none => pure none
  | _ => pure none

/-- Twin of `litToCtorIfNatI`. -/
def litToCtorIfNatI (fe : FEnv) (e : Expr) : CheckCM Expr := do
  match EO.stripTop (e) with
  | .lit (.natVal n) =>
    if natLitStoredF fe then pure (natLitToConstructor n)
    else pure e
  | _ => pure e

/-- Twin of `reduceNatI`. -/
def reduceNatI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match EO.stripTop (e) with
  | .app f₁ b =>
    match EO.stripTop (f₁) with
    | .const c us =>
      match us with
      | _ :: _ => pure none
      | [] => do
        if c == natSuccName ∧ natLitStoredF fe then do
          let w ← r.whnf depth b
          match rawNatLitC? w with
          | some n =>
            if natSizeBytes (n + 1) > fe.limits.natMaxBytes then throw (.invalid natTooBigMsg)
            pure (some (.lit (.natVal (n + 1))))
          | none => pure none
        else pure none
    | .app f₂ a =>
      match EO.stripTop (f₂) with
      | .const cn us =>
        match us with
        | _ :: _ => pure none
        | [] => do
          if (cn == natAddName ∨ cn == natSubName ∨ cn == natMulName ∨
              cn == natPowName ∨ cn == natBeqName ∨ cn == natBleName ∨
              cn == natDivName ∨ cn == natModName ∨ cn == natGcdName ∨
              cn == natLandName ∨ cn == natLorName ∨ cn == natXorName ∨
              cn == natShiftLeftName ∨ cn == natShiftRightName) then do
            -- first argument first; the second only behind a literal
            -- (official `reduce_bin_nat_op`)
            let w₁ ← r.whnf depth a
            match rawNatLitC? w₁ with
            | some n₁ => do
              let w₂ ← r.whnf depth b
              match rawNatLitC? w₂ with
              | some n₂ =>
                if let some msg := natOpRefusal fe.limits.natMaxBytes cn n₁ n₂ then
                  throw (.invalid msg)
                let res := natOpResult cn n₁ n₂
                if natResultRefused fe.limits.natMaxBytes cn res then throw (.invalid natTooBigMsg)
                pure res
              | none => pure none
            | none => pure none
          else if natOpWfNames.contains cn then do
            let w₁ ← r.whnf depth a
            match rawNatLitC? w₁ with
            | some _ => do
              let w₂ ← r.whnf depth b
              match rawNatLitC? w₂ with
              | some _ => throw (.notImplemented
                  s!"native Nat computation on literals ({cn})")
              | none => pure none
            | none => pure none
          else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `iotaCertsFullIAux`. -/
def iotaCertsFullIAux (r : CoreFnsI) (depth : Nat) :
    Expr → List Expr → List Expr → CheckCM Bool
  | _, _, [] => pure true
  | ty, acc, arg :: rest => do
    match EO.stripTop (ty) with
    | .forallE _ dom body _ => do
        let dom' ← instListM dom acc
        let ta ← r.infer depth arg
        if ← r.defeq depth ta dom' then
          iotaCertsFullIAux r depth body (arg :: acc) rest
        else pure false
    | .bvar _ =>
      match acc with
      | [] => pure false
      | _ :: _ => do
        let ty' ← instListM ty acc
        iotaCertsFullIAux r depth ty' [] (arg :: rest)
    | _ => pure false
termination_by _ acc args => (args.length, acc.length)
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.right' <;> simp

/-- Twin of `iotaCertsFullI`. -/
def iotaCertsFullI (r : CoreFnsI) (depth : Nat) (ty : Expr) (args : List Expr) : CheckCM Bool :=
  iotaCertsFullIAux r depth ty [] args

/-- Twin of `defEqListI`. -/
def defEqListI (r : CoreFnsI) (depth : Nat) : List Expr → List Expr → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then defEqListI r depth as bs else pure false
  | _, _ => pure false

/-- Twin of `piResidual` (`piResidualAcc`): the telescope instantiated
along the spine, a `bvar` head re-entering with the accumulator flushed. -/
def piResidual (e : Expr) (args : List Expr) : Option Expr :=
  go [] e args
where
  go : List Expr → Expr → List Expr → Option Expr
    | acc, e, [] => some (e.instI acc.toArray)
    | acc, e, a :: as =>
      match EO.stripTop (e) with
      | .forallE _ _ b _ => go (a :: acc) b as
      | .bvar _ =>
        match acc with
        | [] => none
        | _ :: _ => go [] (e.instI acc.toArray) (a :: as)
      | _ => none
  termination_by acc _ as => (as.length, acc.length)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp +arith +decide)
      | (apply Prod.Lex.left; simp +arith +decide)

/-- Twin of `iotaIndexOkI`. -/
def iotaIndexOkI (r : CoreFnsI) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) : CheckCM Bool :=
  if mI = rP then pure true
  else do
    match piResidual tyCtor margs with
    | some residual => defEqListI r depth ((appArgs residual).drop cnP) idx
    | none => pure false

/-- Twin of `defeqSpineI`. -/
def defeqSpineI (r : CoreFnsI) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  match a.getAppFnT with
  | .const n us =>
    match b.getAppFnT with
    | .const n' us' => do
      let aargs := appArgs a
      let bargs := appArgs b
      if n == n' ∧ aargs.length = bargs.length then
        match ← isEquivListLM us us' with
        -- last to first, as official `is_def_eq_args`
        | some true => defEqListI r depth aargs.reverse bargs.reverse
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `proofIrrelI`. -/
def proofIrrelI (r : CoreFnsI) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  let ta ← r.inferIO depth a
  let tta ← r.inferIO depth ta
  let wtta ← r.whnf depth tta
  match EO.stripTop (wtta) with
  | .sort uT => do
    let okA ← liftFueled "level comparison" (← isEquivLM uT .zero)
    let tb ← r.inferIO depth b
    let ttb ← r.inferIO depth tb
    let wttb ← r.whnf depth ttb
    match EO.stripTop (wttb) with
    | .sort vT => do
      let okB ← liftFueled "level comparison" (← isEquivLM vT .zero)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- Twin of `certAtI`. -/
@[inline] def certAtI (mode : CheckMode) (c : CheckCM Bool) : CheckCM Bool :=
  if mode.verifiedChecks then c else pure true

/-- Twin of `propIrrelI`. -/
def propIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  if (← notProofFastM fe a) || (← notProofFastM fe b) then
    pure false
  else if (← isProofFastM fe a) && (← isProofFastM fe b) then
    pure true
  else proofIrrelI r depth a b

/-- Twin of `projNodesI`. -/
def projNodesI (T : Name) (b : Expr) : List Nat → List Expr
  | [] => []
  | i :: rest => Expr.proj T i b :: projNodesI T b rest

/-- Twin of `structEtaCertWithI`. -/
def structEtaCertWithI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b wtb : Expr) :
    CheckCM Bool := do
  match a.getAppFnT with
  | .const cn us => do
    match fe.ctorView? cn with
    | some (cvc, cnP, cnF) => do
      let aargs := appArgs a
      if aargs.length = cnP + cnF then
        match wtb.getAppFnT with
        | .const Tn us' => do
          match fe.indView? Tn with
          | some (cvT, caps) => do
            let targs := appArgs wtb
            if caps.eta = true ∧ caps.etaCtor == cn ∧
                reservedBasisNames.contains Tn = false ∧
                reservedBasisNames.contains cn = false ∧
                targs.length = caps.etaParams ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams == cvT.levelParams ∧
                fe.towerSlotsAllF Tn caps.etaFields = true then do
              if ← liftFueled "level comparison" (← isEquivListLM us us') then do
                if ← defEqListI r depth (aargs.take caps.etaParams) targs then
                  defEqListI r depth (aargs.drop caps.etaParams)
                    (projNodesI Tn b (List.range caps.etaFields))
                else pure false
              else pure false
            else pure false
          | none => pure false
        | _ => pure false
      else pure false
    | none => pure false
  | _ => pure false

/-- Twin of `structEtaCertI`. -/
def structEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  if etaCtorShapeC fe a then
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    structEtaCertWithI r fe depth a b wtb
  else pure false

/-- Twin of `structUnitCertI`. -/
def structUnitCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  match wta.getAppFnT with
  | .const Tn us' => do
    match fe.indView? Tn with
    | some (cvT, caps) => do
      if caps.unitlike = true ∧
          reservedBasisNames.contains Tn = false ∧
          (appArgs wta).length = caps.unitParams ∧
          us'.length = cvT.levelParams.length then do
        let tb ← r.inferIO depth b
        let wtb ← r.whnf depth tb
        if (EO.stripTop wtb).isForall then pure false else
        r.defeq depth wta wtb
      else pure false
    | none => pure false
  | _ => pure false

/-- Twin of `stuckIrrelI`. -/
def stuckIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  if ← structEtaCertI r fe depth a b then pure true
  else if ← structEtaCertI r fe depth b a then pure true
  else if ← structUnitCertI r fe depth a b then pure true
  else proofIrrelI r depth a b

/-- Twin of `formerSortLoopI`. -/
def formerSortLoopI (wh : Nat → Expr → CheckCM Expr) : Nat → Nat → Expr → CheckCM (Option Level)
  | d, 0, e => do
    match EO.stripTop (← wh d e) with
    | .sort s => pure (some s)
    | _ => pure none
  | d, n + 1, e => do
    match EO.stripTop (← wh d e) with
    | .forallE _ dom b _ => do
      let fv ← mkFVarM d dom
      formerSortLoopI wh (d + 1) n (b.inst1I fv)
    | _ => pure none

/-- Twin of `formerNeverZeroI`. -/
def formerNeverZeroI (wh : Nat → Expr → CheckCM Expr) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) : CheckCM Bool :=
  match formerResSort cvT.type with
  | some _ => pure (formerNeverZero cvT us)
  | none => do
    let ty ← instLevelParamsM cvT.levelParams us cvT.type
    match ← formerSortLoopI wh 0 (caps.nparams + caps.nIdx) ty with
    | some s => pure (Lvl.zeronessOf s).isNever
    | none => pure false

/-- Twin of `iotaCase3I`. -/
def iotaCase3I (wh : Nat → Expr → CheckCM Expr) (fe : FEnv) (isK : Bool)
    (cvj : ConstantVal) (us : List Level) : CheckCM Bool :=
  if isK then pure false else
  match ctorFamily fe cvj with
  | some (cvT, caps) =>
    if cvT.levelParams.length == us.length then do
      let nz ← formerNeverZeroI wh cvT caps us
      pure !nz
    else pure true
  | none => pure true

/-- Twin of `litMajorToCtorI`. -/
def litMajorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) : CheckCM Expr := do
  match EO.stripTop (e) with
  | .lit (.strVal s) =>
    if strLitStoredF fe then r.whnf depth (strLitToConstructor s)
    else pure e
  | _ => litToCtorIfNatI fe e

/-- Twin of `projLitToCtorI`. -/
def projLitToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) : CheckCM Expr := do
  match EO.stripTop (e) with
  | .lit (.strVal s) =>
    if strLitStoredF fe then r.whnf depth (strLitToConstructor s)
    else pure e
  | _ => pure e

/-- Twin of `pinArgsI`: the nested rule's pins at the recursor's levels,
the rule prefix substituted for their loose variables (`instSpineC`);
`none` where a level would pass C's depth bound. -/
def pinArgsI (lps : List Name) (us : List Level) (args : List Expr) : List Expr → Option (List Expr)
  | [] => some []
  | p :: ps => do
    let q ← EO.instLevelParamsChecked? p lps us
    return (q.instI args.toArray.reverse) :: (← pinArgsI lps us args ps)

/-- Twin of `iotaNumArgs`. -/
def iotaNumArgs : Expr → Nat → Nat
  | .mdata _ e, n => iotaNumArgs e n
  | .app f _, n => iotaNumArgs f (n + 1)
  | _, n => n

/-- Twin of `iotaArityOk`. -/
def iotaArityOk (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFnT with
  | .const c us =>
    match fe.recArity? c with
    | some (mI, nL) => iotaNumArgs e 0 == mI + 1 && us.length == nL
    | none => false
  | _ => false

/-- Twin of `projCertF`. -/
def projCertF (fe : FEnv) (c : Name) (args : List Expr) : Bool :=
  match fe.ctorView? c with
  | some (cvC, _, _) => teleArityOk cvC.type args
  | none => false

/-- Twin of `projCertAtF`. -/
def projCertAtF (fe : FEnv) (verified : Bool) (c : Name) (args : List Expr) : Bool :=
  if verified then projCertF fe c args else true

/-- Twin of `ensureSortI`. -/
def ensureSortI (r : CoreFnsI) (depth : Nat) (e : Expr) : CheckCM Level := do
  match EO.stripTop (← r.whnf depth e) with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- Twin of `checkGuardRowsI`. -/
def checkGuardRowsI (inf wh : Nat → Expr → CheckCM Expr) (guardSort : Level) :
    List (Nat × Expr) → CheckCM Unit
  | [] => pure ()
  | (d, dom) :: rest => do
    let t ← inf d dom
    match EO.stripTop (← wh d t) with
    | .sort u =>
      unless Lvl.zeroWhereZero guardSort u do
        throw (.invalid "projection from a propositional structure must be a proposition")
      checkGuardRowsI inf wh guardSort rest
    | _ => throw (.invalid "expected a sort")

/-- Twin of `projGuardSortI`. -/
def projGuardSortI (wh : Nat → Expr → CheckCM Expr) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) : CheckCM (Option Level) :=
  match formerResSort cvT.type with
  | some s => pure (if Lvl.isAlwaysZero s then some .zero else none)
  | none => do
    let ty ← instLevelParamsM cvT.levelParams us cvT.type
    match ← formerSortLoopI wh 0 (caps.nparams + caps.nIdx) ty with
    | some s => pure (if (Lvl.zeronessOf s).isNever then none else some s)
    | none => throw (.invalid "projection from a structure whose type reaches no sort")

/-- Twin of `checkProjRowsI`: the constructor's type at the use's levels, its
parameters opened, then its fields stepped (`projGuardRowsGoM`). -/
def checkProjRowsI (inf wh : Nat → Expr → CheckCM Expr) (fe : FEnv) (entry : ProjEntry)
    (us : List Level) (guardSort : Level) : CheckCM Unit := do
  match fe.find? entry.ctor with
  | some _ => do
    let cty ← constTyAtM fe entry.ctor us
    match ← openPisAtFvarsM entry.numParams cty 0 with
    | some (_, r) =>
      match ← projGuardRowsGoM entry.idx entry.numParams r with
      | some rows => checkGuardRowsI inf wh guardSort rows
      | none =>
        throw (.invalid "projection from a propositional structure must be a proposition")
    | none =>
      throw (.invalid "projection from a propositional structure must be a proposition")
  | none =>
    throw (.invalid "projection from a propositional structure must be a proposition")

/-- Twin of `checkProjGuardI`. -/
def checkProjGuardI (inf wh : Nat → Expr → CheckCM Expr) (fe : FEnv) (entry : ProjEntry)
    (us : List Level) : CheckCM Unit := do
  match fe.indView? entry.structName with
  | some (cvT, caps) => do
    match ← projGuardSortI wh cvT caps us with
    | none => pure ()
    | some guardSort => checkProjRowsI inf wh fe entry us guardSort
  | none => throw (.invalid "projection from a propositional structure must be a proposition")

/-! ### Binder-telescope loops -/

/-- Twin of `inferLamsOutI`. -/
def inferLamsOutI (d : Nat) : List Expr → Nat → Expr → CheckCM Expr
  | [], _j, cur => pure cur
  | tyo :: rest, j, cur => do
    let tyAbs ← abstractRangeM tyo d j
    inferLamsOutI d rest (j - 1) (.forallE .anonymous tyAbs cur .default)

/-- Twin of `inferLamsLeafI`. -/
def inferLamsLeafI (r : CoreFnsI) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Expr) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  let cur ← abstractRangeM bt d k
  inferLamsOutI d stk (k - 1) cur

/-- Twin of `inferLamsI`. -/
def inferLamsI (r : CoreFnsI) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Expr → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match EO.stripTop (t) with
    | .lam _ ty body _ => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      match EO.stripTop (← r.whnf (d + k) tty) with
      | .sort _ => do
        let fv ← mkFVarM (d + k) tyo
        inferLamsI r d fuel body (k + 1) (fvs.push fv) (tyo :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferLamsLeafI r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeafI r d t k fvs stk

/-- Twin of `inferPisOutI`. -/
def inferPisOutI : List Level → Level → Level
  | [], v => v
  | u :: rest, v => inferPisOutI rest (.imax u v)

/-- Twin of `inferPisLeafI`; an `imax` chain past C's depth bound is an
internal error (C's `Level.mkData` would abort). -/
def inferPisLeafI (r : CoreFnsI) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Level) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  match EO.stripTop (← r.whnf (d + k) bt) with
  | .sort v =>
    if EO.imaxChainFits stk v then pure (.sort (inferPisOutI stk v))
    else throw (.internal "universe level too deep")
  | _ => throw (.invalid "expected a sort")

/-- Twin of `inferPisI`. -/
def inferPisI (r : CoreFnsI) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Level → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match EO.stripTop (t) with
    | .forallE _ ty body _ => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      match EO.stripTop (← r.whnf (d + k) tty) with
      | .sort u => do
        let fv ← mkFVarM (d + k) tyo
        inferPisI r d fuel body (k + 1) (fvs.push fv) (u :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferPisLeafI r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeafI r d t k fvs stk

/-- Twin of `defeqArgI`: an `eagerReduce _ _` argument's type is compared
in the eager tower. -/
@[inline] def defeqArgI (r : CoreFnsI) (depth : Nat) (a ta ty : Expr) : CheckCM Bool :=
  if Expr.isEagerReduce a then r.defeqE depth ta ty else r.defeq depth ta ty

/-- Twin of `inferSpineI`. -/
def inferSpineI (r : CoreFnsI) (depth : Nat) : Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match EO.stripTop (ty) with
    | .forallE _ dom body _ => do
      let dom' ← instListRevM dom acc
      let ta ← r.infer depth a
      unless ← defeqArgI r depth a ta dom' do
        throw (.invalid "application type mismatch")
      inferSpineI r depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      match EO.stripTop (← r.whnf depth ty') with
      | .forallE _ dom body _ => do
        let ta ← r.infer depth a
        unless ← defeqArgI r depth a ta dom do
          throw (.invalid "application type mismatch")
        inferSpineI r depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Twin of `inferSpineIOI`. -/
def inferSpineIOI (r : CoreFnsI) (depth : Nat) : Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match EO.stripTop (ty) with
    | .forallE _ _ body _ => inferSpineIOI r depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      match EO.stripTop (← r.whnf depth ty') with
      | .forallE _ _ body _ => inferSpineIOI r depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Twin of `boolTrueShortcutI`. -/
def boolTrueShortcutI (r : CoreFnsI) (depth : Nat) (a : Expr) : CheckCM Bool := do
  pure (Expr.isBoolTrue (← r.whnf depth a))

/-- Twin of `defeqOffsetI`. -/
def defeqOffsetI (r : CoreFnsI) (depth : Nat) (a b : Expr) : CheckCM (Option Bool) :=
  if (Expr.isNatZero a) && (Expr.isNatZero b) then pure (some true) else
  if (Expr.isLitI a) && (Expr.isLitI b) then pure none else
  match (Expr.natPred? a), (Expr.natPred? b) with
  | some x, some y => do pure (some (← r.defeq depth x y))
  | _, _ => pure none

/-- Twin of `tryUnfoldProjAppI`. -/
def tryUnfoldProjAppI (r : CoreFnsI) (depth : Nat) (e : Expr) : CheckCM (Option Expr) :=
  if Expr.headIsProj e then do
    let e' ← r.whnfCore false depth e
    if e' == e then pure none else pure (some e')
  else pure none

/-! ### Mode-dependent bodies -/

section
variable (mode : CheckMode)

/-- Twin of `etaCertI`. -/
def etaCertI (r : CoreFnsI) (depth : Nat) (ty₁ body₁ : Expr) (b : Expr) : CheckCM Bool := do
  if !(Expr.ioNeutral b) then pure false else
  let tb ← r.inferIO depth b
  match EO.stripTop (← r.whnf depth tb) with
  | .forallE _ ty₂ cod₂ _ => do
    if ← r.defeq depth ty₂ ty₁ then do
      let fv ← mkFVarM depth ty₁
      let b₁ := body₁.inst1I fv
      unless ← r.defeq (depth + 1) b₁ (.app b fv) do return false
      if mode.verifiedChecks then do
        let t₁ ← r.infer (depth + 1) b₁
        unless ← r.defeq (depth + 1) t₁ (cod₂.inst1I fv) do return false
      pure true
    else pure false
  | _ => pure false

/-- Twin of `majorToCtorI`. -/
def majorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (isK : Bool)
    (rules : List RecursorRule) (major : Expr) : CheckCM Expr := do
  if isCtorAppC fe major then pure major else
  match rules with
  | [rl] =>
    match fe.ctorView? rl.ctor with
    | some (cvj, cnP, _) =>
      match EO.stripTop ((piResult cvj.type).getAppFnT) with
      | .const T _ =>
        match fe.indView? T with
        | some (cvT, caps) =>
          if isK = true then do
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFnT with
            | .const T' ust =>
              if T' == T ∧ cvj.levelParams.length = ust.length then do
                let margs := appArgs tmaj
                if cnP ≤ margs.length then do
                  let fab ← mkAppNM (.const rl.ctor ust) (margs.take cnP)
                  if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then do
                    -- official `to_cnstr_when_K`'s type check, both modes; the
                    -- proof-irrelevance certificate at the verified mode
                    let tfab ← r.inferIO depth fab
                    if ← r.defeq depth tmaj tfab then
                      if ← certAtI mode (proofIrrelI r depth fab major) then pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if etaRescueOk rl.ctor cvj cvT caps = true then do
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFnT with
            | .const T' ust => do
              let margs := appArgs tmaj
              if T' == T ∧ margs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  reservedBasisNames.contains T = false ∧
                  reservedBasisNames.contains caps.etaCtor = false ∧
                  fe.towerSlotsAllF T caps.etaFields = true then do
                if ← formerNeverZeroI r.whnf cvT caps ust then do
                  let fab ← mkAppNM (.const caps.etaCtor ust)
                    (margs ++ projNodesI T major (List.range caps.etaFields))
                  if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then
                    pure fab
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if T == andName then do
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFnT with
            | .const T' ust => do
              let margs := appArgs tmaj
              if T' == T ∧ margs.length = cnP ∧
                  cvj.levelParams.length = ust.length ∧
                  fe.andRescueSlotsF rl.ctor cnP = true then do
                let fab ← mkAppNM (.const rl.ctor ust) (margs ++ projNodesI T major [0, 1])
                if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then do
                  let tfab ← r.inferIO depth fab
                  if ← r.defeq depth tmaj tfab then
                    if ← certAtI mode (proofIrrelI r depth fab major) then pure fab
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else pure major
        | none => pure major
      | _ => pure major
    | none => pure major
  | _ => pure major

/-- Twin of `prepareMajorI`. -/
def prepareMajorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (isK : Bool)
    (rules : List RecursorRule) (major : Expr) : CheckCM Expr := do
  if isK then do
    let majorK ← majorToCtorI mode r fe depth isK rules major
    if isCtorAppC fe majorK then litMajorToCtorI r fe depth majorK
    else pure majorK
  else do
    let majorE ← if (Expr.isStrLitI major) then pure major
      else majorToCtorI mode r fe depth isK rules major
    if isCtorAppC fe majorE then pure majorE
    else do
      let major₀ ← r.whnf depth majorE
      let major₁ ← litMajorToCtorI r fe depth major₀
      majorToCtorI mode r fe depth isK rules major₁

/-- Twin of `iotaRecI`.  The rule's firing mode is read only inside the
case-3 certificate (`recFireAt`). -/
def iotaRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) : CheckCM (Option Expr) := do
  match e.getAppFnT with
  | .const c us => do
    match fe.recAt? c with
    | some (rv, isQuot) => do
      let mI := majorIdxOf rv
      let rP := rulePrefixOf rv
      let args := appArgs e
      if args.length = mI + 1 ∧ us.length = rv.levelParams.length ∧
          (peelPis (mI + 1) rv.type).isSome = true then do
        let major ← prepareMajorI mode r fe depth rv.k rv.rules (args.getD mI (.bvar 0))
        match major.getAppFnT with
        | .const cj usj => do
          match fe.ctorView? cj with
          | some (cvj, cnP, _) =>
            match rv.rules.find? (fun r' => r'.ctor == cj) with
            | some rl => do
              let margs := appArgs major
              if margs.length = cnP + rl.nfields then do
                if ← certAtI mode (do
                    let fire := recFireAt rv isQuot
                    let cmpLvls : List Level ←
                      match fire with
                      | .nested lvls _ => substLevelTreesM rv.levelParams us lvls
                      | .plain =>
                        substLevelTreesM rv.levelParams us (cvj.levelParams.map Level.param)
                      | .levels lvls => substLevelTreesM rv.levelParams us lvls
                    if ← iotaCase3I r.whnf fe rv.k cvj cmpLvls then do
                      if ← liftFueled "level comparison" (← isEquivListLM usj cmpLvls) then do
                        let cmpArgs : List Expr ←
                          match fire with
                          | .nested _ pins =>
                            match pinArgsI rv.levelParams us (args.take rP) pins with
                            | some ps => pure ps
                            | none => throw (.internal "universe level too deep")
                          | .plain => pure (args.take cnP)
                          | .levels _ => pure (args.take cnP)
                        if ← defEqListI r depth (margs.take cnP) cmpArgs then do
                          let tyCtor ← constTyAtM fe cj usj
                          if ← iotaCertsFullI r depth tyCtor margs then
                            iotaIndexOkI r depth mI rP cnP tyCtor margs ((args.take mI).drop rP)
                          else pure false
                        else pure false
                      else pure false
                    else pure true) then do
                  let rhs ← ruleRhsAtM fe c cj us
                  pure (some (← mkAppNM rhs (args.take rP ++ margs.drop cnP)))
                else pure none
              else pure none
            | none => pure none
          | none => pure none
        | _ => pure none
      else pure none
    | none => pure none
  | _ => pure none

/-- Twin of `reduceProjCoreI`. -/
def reduceProjCoreI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (sn : Name) (i : Nat) (c : Expr) :
    CheckCM (Option Expr) := do
  let e' ← projLitToCtorI r fe depth c
  match fe.findProj? sn i with
  | some entry =>
    match e'.getAppFnT with
    | .const k us => do
      let args := appArgs e'
      if k == entry.ctor ∧ i < entry.numFields ∧
          args.length = entry.numParams + entry.numFields ∧
          us.length = entry.levelParams.length then do
        let arg := args.getD (entry.numParams + i) (.bvar 0)
        if projCertAtF fe mode.verifiedChecks k args then pure (some arg)
        else pure none
      else pure none
    | _ => pure none
  | none => pure none

/-- Twin of `betaPeelI`. -/
def betaPeelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → List Expr → List Expr → CheckCM WhnfStep
  | t, acc, [] => do pure (.cont (← instListM t acc))
  | t, acc, a :: rest => do
    match EO.stripTop (t) with
    | .lam _ _ body _ => betaPeelI r fe depth body (a :: acc) rest
    | _ => do
      let e' ← instListM t acc
      pure (.cont (← mkAppNM e' (a :: rest)))

/-- The name of a term's head constant (`.anonymous` for another head). -/
def headConstName (e : Expr) : Name :=
  match e.getAppFnT with
  | .const n _ => n
  | _ => .anonymous

/-- Twin of `whnfAppI`; a ι step is reported to the poll (`Event.unfold`). -/
def whnfAppI (r : CoreFnsI) (fe : FEnv) (depth : Nat) : Expr → List Expr → CheckCM WhnfStep
  | v, [] => pure (.done v)
  | v, a :: rest => do
    match EO.stripTop (v) with
    | .lam _ _ body _ => betaPeelI r fe depth body [a] rest
    | _ => do
      let fa := Expr.app v a
      match ← (if iotaArityOk fe fa then iotaRecI mode r fe depth fa else pure none) with
      | some e'' =>
        let e' ← mkAppNM e'' rest
        pollC fe (.unfold (headConstName fa)) (pure (.cont e'))
      | none => whnfAppI r fe depth fa rest

/-- Twin of `whnfCoreStepI`; `mdata` is looked through. -/
@[inline] def whnfCoreStepI (r : CoreFnsI) (fe : FEnv) (cheap : Bool) (depth : Nat)
    (e : Expr) : CheckCM WhnfStep := do
    match EO.stripTop (e) with
    | .sort _ | .fvar .. | .forallE .. | .lam .. | .const .. | .lit _ => pure (.done e)
    | .app _ _ => do
      let v ← r.whnfCore cheap depth e.getAppFnT
      whnfAppI mode r fe depth v (appArgs e)
    | .proj sn i pe => do
      let c ← if cheap then r.whnfCore true depth pe else r.whnf depth pe
      match ← reduceProjCoreI mode r fe depth sn i c with
      | some m' => pure (.cont m')
      | none => pure (.done e)
    | .letE _ _ v b _ => pure (.cont (b.inst1I v))
    | .mdata _ b => pure (.cont b)
    | .bvar _ | .mvar _ => throw (.notImplemented "whnf beyond the supported fragment")

/-- Twin of `whnfCoreLoopI`. -/
def whnfCoreLoopI (r : CoreFnsI) (fe : FEnv) (cheap : Bool) (depth : Nat) :
    Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e => do
    match ← whnfCoreStepI mode r fe cheap depth e with
    | .done v => pure v
    | .cont e' => whnfCoreLoopI r fe cheap depth n e'

/-- Twin of `whnfCoreBodyI`. -/
def whnfCoreBodyI (r : CoreFnsI) (fe : FEnv) : Bool → Nat → Expr → CheckCM Expr :=
  fun cheap depth e => whnfCoreLoopI mode r fe cheap depth whnfCoreLoopFuel e

end

/-- Twin of `whnfStepI`. -/
@[inline] def whnfStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Expr → CheckCM Expr) (e : Expr) : CheckCM Expr := do
  let e₁ ← r.whnfCore false depth e
  match ← reduceNatI r fe depth e₁ with
  | some e₂ => k e₂
  | none =>
    match ← unfoldDefinitionI fe e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- Twin of `whnfLoopI`. -/
def whnfLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) : Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStepI r fe depth (whnfLoopI r fe depth n) e

/-- Twin of `whnfBodyI`. -/
def whnfBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => whnfLoopI r fe depth whnfLoopFuel e

/-- The safety checks of official `infer_constant`. -/
def checkConstSafety (fe : FEnv) (n : Name) (ci : ConstantInfo) : CheckCM Unit := do
  if ci.isUnsafe && fe.safety != .unsafe then
    throw (.invalid s!"invalid declaration, it uses unsafe declaration '{n}'")
  if let .defnInfo v := ci then
    if v.safety == .partial && fe.safety == .safe then
      throw (.invalid s!"invalid declaration, safe declaration must not contain partial declaration '{n}'")

/-- Twin of `inferBodyI`; a sort's successor past C's depth bound is an
internal error. -/
def inferBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match EO.stripTop (e) with
    | .sort u =>
      if EO.depthFits 1 u then pure (.sort (.succ u))
      else throw (.internal "universe level too deep")
    | .fvar id =>
      match fvarDepth? id with
      | some i =>
        if i < depth then
          match ← fvarTypeM? id with
          | some ty => pure ty
          | none => throw (.internal "an interned free variable without its type")
        else throw (.invalid "free variable out of scope")
      | none => throw (.invalid "free variable out of scope")
    | .const n us => do
      match fe.find? n with
      | none => throw (unknownConstError fe n)
      | some ci =>
        unless us.length = ci.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        checkConstSafety fe n ci
        constTyAtM fe n us
    | .lit (.natVal n) => do
      if natSizeBytes n > fe.limits.natMaxBytes then throw (.invalid natTooBigMsg)
      if natLitStoredF fe then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitStoredF fe then pure (.const stringName [])
      else throw (.notImplemented "string literals before the String support declarations")
    | .forallE _ ty body _ => do
      let tty ← r.infer depth ty
      match EO.stripTop (← r.whnf depth tty) with
      | .sort u => do
        let fv ← mkFVarM depth ty
        inferPisI r depth (← peelFuelM) body 1 #[fv] [u]
      | _ => throw (.invalid "expected a sort")
    | .lam _ ty body _ => do
      let tty ← r.infer depth ty
      match EO.stripTop (← r.whnf depth tty) with
      | .sort _ => do
        let fv ← mkFVarM depth ty
        inferLamsI r depth (← peelFuelM) body 1 #[fv] [ty]
      | _ => throw (.invalid "expected a sort")
    | .app _ _ => do
      let tf ← r.infer depth e.getAppFnT
      inferSpineI r depth tf #[] (appArgs e)
    | .proj sn i pe => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match te.getAppFnT with
      | .const T us => do
        match fe.findProj? T i with
        | some entry => do
          let targs := appArgs te
          unless T == sn do
            throw (.invalid "invalid projection: the node names another structure")
          unless targs.length = entry.numParams do
            throw (.invalid "projection parameter mismatch")
          if us.length = entry.levelParams.length then do
            checkProjGuardI r.inferIO r.whnf fe entry us
            match entry.typeAtI us targs pe with
            | some ty => pure ty
            | none => throw (.internal "projection body unreadable")
          else throw (.notImplemented "projection without a native entry")
        | none =>
          throw (projMissError fe (fe.hasTable T) T sn i (appArgs te).length)
      | _ => throw (.invalid "invalid projection: not a structure-like type, or no such field")
    | .letE _ ty v b _ => do
      let tty ← r.infer depth ty
      let _ ← ensureSortI r depth tty
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      r.infer depth (b.inst1I v)
    | .mdata _ b => r.infer depth b
    | .bvar _ | .mvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- Twin of `inferBodyIOI`; an `imax` past C's depth bound is an internal
error. -/
def inferBodyIOI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match EO.stripTop (e) with
    | .app _ _ => do
      let tf ← r.infer depth e.getAppFnT
      inferSpineIOI r depth tf #[] (appArgs e)
    | .forallE _ ty body _ => do
      let tty ← r.infer depth ty
      match EO.stripTop (← r.whnf depth tty) with
      | .sort u => do
        let fv ← mkFVarM depth ty
        let bt ← r.infer (depth + 1) (body.inst1I fv)
        let v ← ensureSortI r (depth + 1) bt
        if EO.imaxChainFits [u] v then pure (.sort (.imax u v))
        else throw (.internal "universe level too deep")
      | _ => throw (.invalid "expected a sort")
    | .lam _ ty body _ => do
      let fv ← mkFVarM depth ty
      let bt ← r.infer (depth + 1) (body.inst1I fv)
      let bAbs ← abstract1M bt depth
      pure (.forallE .anonymous ty bAbs .default)
    | .letE _ _ v b _ => r.infer depth (b.inst1I v)
    | .mdata _ b => r.infer depth b
    | _ => inferBodyI r fe depth e

section
variable (mode : CheckMode)

/-- Twin of `defeqLamsInnerI`. -/
def defeqLamsInnerI (r : CoreFnsI) (depth : Nat) (b₁ b₂ : Expr) : CheckCM Bool := do
  unless ← r.defeq (depth + 1) b₁ b₂ do return false
  if mode.verifiedChecks then do
    let t₁ ← r.infer (depth + 1) b₁
    let t₂ ← r.infer (depth + 1) b₂
    unless ← r.defeq (depth + 1) t₁ t₂ do return false
  pure true

/-- Twin of `defeqLamsI`. -/
def defeqLamsI (r : CoreFnsI) : Nat → Nat → Expr → Expr → Expr → Expr → CheckCM Bool
  | fuel, depth, ty₁, body₁, ty₂, body₂ => do
    unless ← r.defeq depth ty₁ ty₂ do return false
    let fv ← mkFVarM depth ty₂
    let b₁ := body₁.inst1I fv
    let b₂ := body₂.inst1I fv
    match fuel, Expr.lamPair? b₁ b₂ with
    | fuel + 1, some (ty₁', body₁', ty₂', body₂') =>
      if b₁ == b₂ then pure true
      else defeqLamsI r fuel (depth + 1) ty₁' body₁' ty₂' body₂'
    | _, _ => defeqLamsInnerI mode r depth b₁ b₂

/-- Twin of `quickDefEqI`. -/
def quickDefEqI (r : CoreFnsI) (depth : Nat) (a b : Expr) : CheckCM (Option Bool) :=
  if a == b then pure (some true) else
  match EO.stripTop a, EO.stripTop b with
  | .sort u, .sort v => do pure (some (← liftFueled "level comparison" (← isEquivLM u v)))
  | .lit l₁, .lit l₂ => pure (some (l₁ == l₂))
  | .forallE _ ty₁ body₁ _, .forallE _ ty₂ body₂ _ => do
    unless ← r.defeq depth ty₁ ty₂ do return some false
    let fv ← mkFVarM depth ty₂
    unless ← r.defeq (depth + 1) (body₁.inst1I fv) (body₂.inst1I fv) do return some false
    pure (some true)
  | .lam _ ty₁ body₁ _, .lam _ ty₂ body₂ _ => do
    pure (some (← defeqLamsI mode r lamsFuel depth ty₁ body₁ ty₂ body₂))
  | _, _ => pure none

/-- Twin of `deltaQuickI`. -/
def deltaQuickI (r : CoreFnsI) (depth : Nat) (a b : Expr) : CheckCM DeltaStep := do
  match ← quickDefEqI mode r depth a b with
  | some true => pure .eq
  | some false => pure .diff
  | none => pure (.cont a b)

/-- Twin of `lazyDeltaStepI`. -/
def lazyDeltaStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) : CheckCM DeltaStep := do
  match unfoldableHeadC fe a, unfoldableHeadC fe b with
  | false, false => pure .unknown
  | true, false =>
    match ← tryUnfoldProjAppI r depth b with
    | some b₂ => deltaQuickI mode r depth a b₂
    | none =>
      match ← unfoldDefinitionI fe a with
      | some a₂ => deltaQuickI mode r depth (← r.whnfCore true depth a₂) b
      | none => pure .unknown
  | false, true =>
    match ← tryUnfoldProjAppI r depth a with
    | some a₂ => deltaQuickI mode r depth a₂ b
    | none =>
      match ← unfoldDefinitionI fe b with
      | some b₂ => deltaQuickI mode r depth a (← r.whnfCore true depth b₂)
      | none => pure .unknown
  | true, true => do
    let ha := headHintC fe a
    let hb := headHintC fe b
    if hintLt hb ha then
      match ← unfoldDefinitionI fe a with
      | some a₂ => deltaQuickI mode r depth (← r.whnfCore true depth a₂) b
      | none => pure .unknown
    else if hintLt ha hb then
      match ← unfoldDefinitionI fe b with
      | some b₂ => deltaQuickI mode r depth a (← r.whnfCore true depth b₂)
      | none => pure .unknown
    else if ← (if hintSameRegular ha hb && sameConstHeadsC a b then
        defeqSpineI r depth a b else pure false) then pure .eq
    else
      match ← unfoldDefinitionI fe a, ← unfoldDefinitionI fe b with
      | some a₂, some b₂ => do
        let a₃ ← r.whnfCore true depth a₂
        let b₃ ← r.whnfCore true depth b₂
        deltaQuickI mode r depth a₃ b₃
      | _, _ => pure .unknown

/-- Twin of `lazyDeltaReductionI`. -/
def lazyDeltaReductionI (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → Expr → Expr → CheckCM LazyRes
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | n + 1, a, b => do
    match ← defeqOffsetI r depth a b with
    | some v => pure (.verdict v)
    | none =>
    -- the eager flag folds with free variables present
    let fold := eager || (!a.hasFVar && !b.hasFVar)
    match ← (if fold then reduceNatI r fe depth a else pure none) with
    | some a₂ => pure (.verdict (← r.defeq depth a₂ b))
    | none =>
    match ← (if fold then reduceNatI r fe depth b else pure none) with
    | some b₂ => pure (.verdict (← r.defeq depth a b₂))
    | none =>
    match ← lazyDeltaStepI mode r fe depth a b with
    | .cont a' b' => lazyDeltaReductionI eager r fe depth n a' b'
    | .eq => pure (.verdict true)
    | .diff => pure (.verdict false)
    | .unknown => pure (.unknown a b)

/-- Twin of `lazyDeltaProjReductionI`. -/
def lazyDeltaProjReductionI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (sn : Name) (i : Nat) :
    Nat → Expr → Expr → CheckCM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: lazy delta projection loop")
  | n + 1, a, b => do
    match ← lazyDeltaStepI mode r fe depth a b with
    | .cont a' b' => lazyDeltaProjReductionI r fe depth sn i n a' b'
    | .eq => pure true
    | .diff | .unknown =>
      match ← reduceProjCoreI mode r fe depth sn i a with
      | some x =>
        match ← reduceProjCoreI mode r fe depth sn i b with
        | some y => r.defeq depth x y
        | none => r.defeq depth a b
      | none => r.defeq depth a b

/-- Twin of `defeqProjPairI`. -/
def defeqProjPairI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) : CheckCM Bool :=
  match EO.stripTop a, EO.stripTop b with
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
    if s₁ == s₂ && i₁ == i₂ then
      lazyDeltaProjReductionI mode r fe depth s₁ i₁ defeqLoopFuel e₁ e₂
    else pure false
  | _, _ => pure false

/-- Twin of `defeqStuckI`; two free variables are compared by depth, as
con-leche compares its levels. -/
def defeqStuckI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) : CheckCM Bool :=
  match EO.stripTop a, EO.stripTop b with
  | .lit l, .app fO _ => do
    match l, EO.stripTop fO with
    | .strVal s, .const cO usO =>
      if cO == stringOfListName ∧ usO = [] ∧ strLitStoredF fe then
        r.defeq depth (strLitToConstructor s) b
      else stuckIrrelI r fe depth a b
    | _, _ => stuckIrrelI r fe depth a b
  | .app fO _, .lit l => do
    match l, EO.stripTop fO with
    | .strVal s, .const cO usO =>
      if cO == stringOfListName ∧ usO = [] ∧ strLitStoredF fe then
        r.defeq depth a (strLitToConstructor s)
      else stuckIrrelI r fe depth a b
    | _, _ => stuckIrrelI r fe depth a b
  | .fvar i, .fvar j =>
    if fvarDepth? i == fvarDepth? j then pure true
    else stuckIrrelI r fe depth a b
  | .const n us, .const n' us' =>
    if n == n' then do
      if ← liftFueled "level comparison" (← isEquivListLM us us') then pure true
      else stuckIrrelI r fe depth a b
    else stuckIrrelI r fe depth a b
  | .app .., .app .. => do
    let as₁ := appArgs a
    let as₂ := appArgs b
    if as₁.length = as₂.length then do
      if ← r.defeq depth a.getAppFnT b.getAppFnT then do
        if ← defEqListI r depth as₁ as₂ then pure true
        else stuckIrrelI r fe depth a b
      else stuckIrrelI r fe depth a b
    else stuckIrrelI r fe depth a b
  | .lam _ ty₁ body₁ _, _ => do
    if ← etaCertI mode r depth ty₁ body₁ b then pure true
    else stuckIrrelI r fe depth a b
  | _, .lam _ ty₂ body₂ _ => do
    if ← etaCertI mode r depth ty₂ body₂ a then pure true
    else stuckIrrelI r fe depth a b
  | _, _ => stuckIrrelI r fe depth a b

/-- Twin of `defeqBodyI`. -/
def defeqBodyI (eager : Bool) (r : CoreFnsI) (fe : FEnv) : Nat → Expr → Expr → CheckCM Bool :=
  fun depth a b => do
    if a == b then pure true else
    -- the eq-true shortcut
    if ← (if Expr.isBoolTrue b && (eager || !a.hasFVar) then boolTrueShortcutI r depth a
        else pure false) then pure true else
    match ← quickDefEqI mode r depth a b with
    | some v => pure v
    | none =>
    -- proof irrelevance before any head normalisation
    if ← propIrrelI r fe depth a b then pure true else
    let a' ← r.whnfCore true depth a
    let b' ← r.whnfCore true depth b
    match ← quickDefEqI mode r depth a' b' with
    | some v => pure v
    | none =>
    match ← lazyDeltaReductionI mode eager r fe depth defeqLoopFuel a' b' with
    | .verdict v => pure v
    | .unknown a₁ b₁ =>
    if ← defeqProjPairI mode r fe depth a₁ b₁ then pure true else
    if !(Expr.headIsProj a₁) && !(Expr.headIsProj b₁) then
      defeqStuckI mode r fe depth a₁ b₁ else
    let a₂ ← r.whnfCore false depth a₁
    let b₂ ← r.whnfCore false depth b₁
    if a₂ == a₁ && b₂ == b₁ then defeqStuckI mode r fe depth a₁ b₁
    else r.defeq depth a₂ b₂

end

/-! ## The memoised knot -/

/-- Twin of `memoEI`. -/
@[inline] def memoEI (get' : CState → Std.HashMap EKey Expr)
    (set' : CState → Std.HashMap EKey Expr → CState)
    (f : Nat → Expr → CheckCM Expr) : Nat → Expr → CheckCM Expr :=
  fun d e => do
    match (get' (← get))[EKey.mk e]? with
    | some r => pure r
    | none =>
      let r ← f d e
      modify fun st =>
        let mp := get' st
        let st := set' st ∅
        set' st (mp.insert (EKey.mk e) r)
      pure r

/-- Twin of `memoBI`. -/
@[inline] def memoBI (f : Nat → Expr → Expr → CheckCM Bool) : Nat → Expr → Expr → CheckCM Bool :=
  fun d a b => do
    match (← get).defeqC[(EKey.mk a, EKey.mk b)]? with
    | some r => pure r
    | none =>
      let r ← f d a b
      modify fun st =>
        let mp := st.defeqC
        let st := { st with defeqC := ∅ }
        { st with defeqC := mp.insert (EKey.mk a, EKey.mk b) r }
      pure r


/-- Twin of `knotLevelI`; every body runs behind the poll (`pollC`). -/
@[inline] def knotLevelI (mode : CheckMode) (eager : Bool) (fe : FEnv)
    (prev prevE : Unit → CoreFnsI) : CoreFnsI :=
  { whnfCore := fun c => if c then
        memoEI (·.whnfCoreCheapC) (fun st mp => { st with whnfCoreCheapC := mp })
          (fun d e => pollC fe (.body d) (whnfCoreBodyI mode (prev ()) fe true d e))
      else memoEI (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp })
        (fun d e => pollC fe (.body d) (whnfCoreBodyI mode (prev ()) fe false d e))
    whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
      (fun d e => pollC fe (.body d) (whnfBodyI (prev ()) fe d e))
    infer := memoEI (·.inferC) (fun st mp => { st with inferC := mp })
      (fun d e => pollC fe (.body d) (inferBodyI (prev ()) fe d e))
    defeq := memoBI (fun d a b => pollC fe (.body d) (defeqBodyI mode eager (prev ()) fe d a b))
    defeqE := fun d a b => withEagerMemos eager
      (memoBI (fun d a b => pollC fe (.body d) (defeqBodyI mode true (prevE ()) fe d a b)) d a b)
    inferIO := memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
      (fun d e => pollC fe (.body d) (inferBodyIOI (prev ()).ioView fe d e)) }

/-- Twin of `knotZeroI`: the fuel is the core's nesting depth, so running
out of it is the recursion limit (`Limits.recDepth`). -/
def knotZeroI : CoreFnsI :=
  { whnfCore := fun _ _ _ => throw (.limit .recDepth)
    whnf := fun _ _ => throw (.limit .recDepth)
    infer := fun _ _ => throw (.limit .recDepth)
    defeq := fun _ _ _ => throw (.limit .recDepth)
    defeqE := fun _ _ _ => throw (.limit .recDepth)
    inferIO := fun _ _ => throw (.limit .recDepth) }

/-- Twin of `knotEagerI`. -/
def knotEagerI (mode : CheckMode) (fe : FEnv) : Nat → CoreFnsI
  | 0 => knotZeroI
  | fuel + 1 => knotLevelI mode true fe (fun _ => knotEagerI mode fe fuel)
      (fun _ => knotEagerI mode fe fuel)

/-- Twin of `knotPlainI`. -/
def knotPlainI (mode : CheckMode) (fe : FEnv) : Nat → CoreFnsI
  | 0 => knotZeroI
  | fuel + 1 => knotLevelI mode false fe (fun _ => knotPlainI mode fe fuel)
      (fun _ => knotEagerI mode fe fuel)

/-- Twin of `coreKnotI`. -/
def coreKnotI (mode : CheckMode) (eager : Bool) (fe : FEnv) (fuel : Nat) : CoreFnsI :=
  match eager with
  | false => knotPlainI mode fe fuel
  | true => knotEagerI mode fe fuel

end Lean.Kernel.InLean
