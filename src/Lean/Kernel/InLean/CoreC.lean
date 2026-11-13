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
and in its shape: the knot is one block of mutually recursive functions
(the entry points `whnfCoreI`, `whnfI`, `inferI`, `defeqI`, `defeqEI` and
the bodies they run), each taking the knot's address (the mode, the
environment, the tower flag and the level); the entry points are memoised
in `CState`.  Each
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
* The refusals at the maximum `Nat` size (`natOpRefusal`,
  `natResultRefused`, the inference of a literal past `Limits.maxNatSize`)
  carry the official kernel's messages.
* The official kernel's resource limits (`Limits`): the knot's level is the
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
/-- Twin of `bindersFuel`. -/
@[irreducible, noinline] def bindersFuel : Nat := 4611686018427387904  -- 2^62
/-- Twin of `unitLikeFuel`. -/
@[irreducible, noinline] def unitLikeFuel : Nat := 4611686018427387904  -- 2^62
/-- Twin of `defeqLoopFuel`. -/
@[irreducible, noinline] def defeqLoopFuel : Nat := 4611686018427387904  -- 2^62
/-- Twin of `checkFuel`. -/
@[irreducible, noinline] def checkFuel : Nat := 4611686018427387904  -- 2^62


/-! ## The helper twins outside the knot -/

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

/-! ### Knot-free helpers -/

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
    if fe.natLit then pure (natLitToConstructor n)
    else pure e
  | _ => pure e

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

/-- Twin of `certAtI`. -/
@[inline] def certAtI (mode : CheckMode) (c : CheckCM Bool) : CheckCM Bool :=
  if mode.verifiedChecks then c else pure true

/-- Twin of `projNodesI`. -/
def projNodesI (T : Name) (b : Expr) : List Nat → List Expr
  | [] => []
  | i :: rest => Expr.proj T i b :: projNodesI T b rest

/-- **Twin of `unitLikeShapeF`**, read off Lean's entries as `structEtaCertWithI`
reads them (`indView?`, `findTable?`, `ctorView?`): the constructor and the
field count are the family's projection table's, at every field count.  In
the monad for the level instantiation, an error past C's depth bound
(`instLevelParamsM`), as every instantiation of a stored type here. -/
def unitLikeShapeM (fe : FEnv) (w : Expr) : CheckCM (Option (Expr × Nat)) :=
  match w.getAppFnT with
  | .const S us =>
    match fe.indView? S with
    | some (cvS, caps) =>
      if caps.eta = true ∧ us.length = cvS.levelParams.length then
        match fe.findTable? S with
        | some tbl =>
          if (appArgs w).length = tbl.numParams then
            match fe.ctorView? tbl.ctor with
            | some (cvC, _, _, _) => do
              let cty ← instLevelParamsM cvC.levelParams us cvC.type
              pure ((peelPis tbl.numParams cty).map fun body =>
                (body.instI (appArgs w).reverse.toArray, tbl.numFields))
            | none => pure none
          else pure none
        | none => pure none
      else pure none
    | none => pure none
  | _ => pure none

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

/-- Twin of `getAppArgsArrGo`; `mdata` read through. -/
def getAppArgsArrGo : Expr → Nat → Array Expr → Array Expr
  | .app f a, i + 1, acc => getAppArgsArrGo f i (acc.set! i a)
  | .mdata _ e, i, acc => getAppArgsArrGo e i acc
  | _, _, acc => acc

/-- Twin of `getAppArgsArr`: the spine's arguments (outermost last), written
into an array of the spine's length from the back: no list is built. -/
@[inline] def getAppArgsArr (e : Expr) : Array Expr :=
  getAppArgsArrGo e (iotaNumArgs e 0) (Array.replicate (iotaNumArgs e 0) e)

/-- Twin of `spineArg`. -/
def spineArg (args : Array Expr) (i : Nat) : Expr := args.getD i (.bvar 0)

/-- Twin of `mkAppRange`: `f` applied to `args[i:j]`, the range read in
place. -/
def mkAppRange (f : Expr) (args : Array Expr) (i j : Nat) : Expr :=
  if h : i < j ∧ i < args.size then mkAppRange (.app f args[i]) args (i + 1) j else f
termination_by j - i

/-- Twin of `iotaArityOk`. -/
def iotaArityOk (fe : FEnv) (e : Expr) : Bool :=
  match e.getAppFnT with
  | .const c us =>
    match fe.recArity? c with
    | some (mI, nL) => iotaNumArgs e 0 == mI + 1 && us.length == nL
    | none => false
  | _ => false

/-- Twin of `isStuckHeadC`: a spine head that is its own head normal form
and not a lambda (the heads `whnfCoreEasy` answers with themselves, but a
lambda). -/
def isStuckHeadC : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .const .. | .lit _ => true
  | _ => false

/-- Twin of `iotaTargetF`: the spine length `mI + 1` at which `iotaRecI`
can fire, where the head is a stored recursor at its own number of levels
(the arity test of `iotaArityOk`, read off the head once). -/
def iotaTargetF (fe : FEnv) (h : Expr) : Option Nat :=
  match h with
  | .const c us =>
    match fe.recArity? c with
    | some (mI, nL) => if us.length = nL then some (mI + 1) else none
    | none => none
  | _ => none

/-- Twin of `projCertF`. -/
def projCertF (fe : FEnv) (c : Name) (args : List Expr) : Bool :=
  match fe.ctorView? c with
  | some (cvC, _, _, _) => teleArityOk cvC.type args
  | none => false

/-- Twin of `projCertAtF`. -/
def projCertAtF (fe : FEnv) (verified : Bool) (c : Name) (args : List Expr) : Bool :=
  if verified then projCertF fe c args else true

/-- Twin of `inferLamsOutI`. -/
def inferLamsOutI (d : Nat) : List Expr → Nat → Expr → CheckCM Expr
  | [], _j, cur => pure cur
  | tyo :: rest, j, cur => do
    let tyAbs ← abstractRangeM tyo d j
    inferLamsOutI d rest (j - 1) (.forallE .anonymous tyAbs cur .default)

/-- Twin of `inferPisOutI`. -/
def inferPisOutI : List Level → Level → Level
  | [], v => v
  | u :: rest, v => inferPisOutI rest (.imax u v)

/-- The name of a term's head constant (`.anonymous` for another head). -/
def headConstName (e : Expr) : Name :=
  match e.getAppFnT with
  | .const n _ => n
  | _ => .anonymous

/-- The safety checks of official `infer_constant`. -/
def checkConstSafety (fe : FEnv) (n : Name) (ci : ConstantInfo) : CheckCM Unit := do
  if ci.isUnsafe && fe.safety != .unsafe then
    throw (.invalid s!"invalid declaration, it uses unsafe declaration '{n}'")
  if let .defnInfo v := ci then
    if v.safety == .partial && fe.safety == .safe then
      throw (.invalid s!"invalid declaration, safe declaration must not contain partial declaration '{n}'")

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

/-- Twin of `whnfCoreEasy` (official `whnf_core`'s easy cases): the kinds
`whnfCoreStepI` answers with `.done e` at the node itself.  The knot returns
them before the memo and the poll.  An `mdata` node is not easy: it goes
through the memo, keyed with its wrapper, as before. -/
@[inline] def whnfCoreEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lam .. | .const .. | .lit _ => true
  | _ => false

/-- Twin of `whnfCoreKeyC`: a term of an arm official `whnf_core` stores (a
projection, a let-expression, or an application whose head is not its own
head normal form), read through its top `mdata`; `h` is its spine head
(`getAppFnT`). -/
@[inline] def whnfCoreKeyC (h e : Expr) : Bool :=
  match EO.stripTop e with
  | .app _ _ => !isStuckHeadC h
  | .proj .. | .letE .. => true
  | _ => false

/-- Twin of `whnfCoreStoresDone`: a key whose step ended the chain with `v`
is stored, but for an application answered by itself. -/
@[inline] def whnfCoreStoresDone (key : Bool) (e v : Expr) : Bool :=
  match EO.stripTop e with
  | .app .. => key && !(v == e)
  | _ => key

/-- Twin of `whnfCoreCheapSafeC`: a step the two modes take alike (a
let-expression, or an application whose head is a lambda or stuck), read
through the top `mdata`. -/
@[inline] def whnfCoreCheapSafeC (h e : Expr) : Bool :=
  match EO.stripTop e with
  | .app _ _ =>
    match h with
    | .lam .. => true
    | h => isStuckHeadC h
  | .letE .. => true
  | _ => false

/-- Twin of `storeChain`: the chain's keys `pend` map to its answer in the
full mode's memo, those of `pendC` in the cheap mode's; each map is taken
out of the state before the inserts. -/
@[inline] def storeChain (st : CState) (pend pendC : List Expr) (v : Expr) : CState :=
  let mp := st.whnfCoreC
  let st := { st with whnfCoreC := ∅ }
  let st := { st with whnfCoreC := pend.foldl (fun m k => m.insert (EKey.mk k) v) mp }
  let mc := st.whnfCoreCheapC
  let st := { st with whnfCoreCheapC := ∅ }
  { st with whnfCoreCheapC := pendC.foldl (fun m k => m.insert (EKey.mk k) v) mc }

/-- Twin of `pushKey`. -/
@[inline] def pushKey (b : Bool) (e : Expr) (pend : List Expr) : List Expr :=
  if b then e :: pend else pend

/-- Twin of `pushCheapKey`. -/
@[inline] def pushCheapKey (safe b : Bool) (e : Expr) (pendC : List Expr) : List Expr :=
  if safe then pushKey b e pendC else []

/-- Twin of `storeChainI`: the cheap mode stores nothing, and a chain without
keys has nothing to store. -/
@[inline] def storeChainI (cheap : Bool) (pend pendC : List Expr) (v : Expr) : CheckCM Unit :=
  if cheap || pend.isEmpty then pure () else modify fun st => storeChain st pend pendC v

/-- Twin of `whnfCoreLookupI`. -/
@[inline] def whnfCoreLookupI (cheap : Bool) (e : Expr) : CheckCM (Option Expr) := do
  let st ← get
  if cheap then pure st.whnfCoreCheapC[EKey.mk e]? else pure st.whnfCoreC[EKey.mk e]?

/-- Twin of `whnfEasy` (official `whnf`'s easy cases): sorts, free
variables, Π-types and literals.  A constant or a lambda-expression still
goes through the memo, as in official `whnf`. -/
@[inline] def whnfEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lit _ => true
  | _ => false

/-! ## The knot

Twin of the cached knot: one block of mutually recursive functions, the five
entry points at its end (`whnfCoreI`, `whnfI`, `inferI`, `defeqI`,
`defeqEI`), each memoised in `CState`, and the bodies and helpers they run.
Every function of the block takes the knot's address: the mode and the
environment (the section's variables), the tower flag `eager` and the level
`lv`.  An entry point at `lv + 1` runs its body at `lv`, behind the poll
(`pollC`); a helper calls the entry points at its own level; at level `0`
every entry point is the recursion limit (`Limits.recDepth`).  Nothing is
built per call: no record, no closure.

Termination is lexicographic: the level, then the helper's place in the
block (an entry point is `0`; a helper calls only helpers above it and the
entry points), then the helper's own loop measure; the ranks are master's. -/

section Knot

variable (mode : CheckMode) (fe : FEnv)

-- Both limits count per command, and the block is one command (each
-- definition alone is far below the defaults): the heartbeats for their
-- elaboration, the recursion depth for the termination proofs over the
-- block's packed argument.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
mutual


/-- Twin of `reduceNatI`. -/
def reduceNatI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match EO.stripTop (e) with
  | .app f₁ b =>
    match EO.stripTop (f₁) with
    | .const c us =>
      match us with
      | _ :: _ => pure none
      | [] => do
        if c == natSuccName ∧ fe.natLit then do
          let w ← whnfI eager lv depth b
          match rawNatLitC? w with
          | some n =>
            if natSizeBytes (n + 1) > fe.limits.maxNatSize then throw (.invalid natTooBigMsg)
            pure (some (.lit (.natVal (n + 1))))
          | none => pure none
        else pure none
    | .app f₂ a =>
      match EO.stripTop (f₂) with
      | .const cn us =>
        match us with
        | _ :: _ => pure none
        | [] => do
          -- the operation found once, by the name's cached hash (`NatBinOp.ofName?`)
          match NatBinOp.ofName? cn with
          | some op => do
            -- first argument first; the second only behind a literal
            -- (official `reduce_bin_nat_op`)
            let w₁ ← whnfI eager lv depth a
            match rawNatLitC? w₁ with
            | some n₁ => do
              let w₂ ← whnfI eager lv depth b
              match rawNatLitC? w₂ with
              | some n₂ =>
                if let some msg := natOpRefusal fe.limits.maxNatSize op n₁ n₂ then
                  throw (.invalid msg)
                let res := op.result n₁ n₂
                if natResultRefused fe.limits.maxNatSize op res then throw (.invalid natTooBigMsg)
                pure (some res)
              | none => pure none
            | none => pure none
          | none => pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none
termination_by (lv, 1, 0, 0)

/-- Twin of `iotaCertsFullIAux`. -/
def iotaCertsFullIAux (eager : Bool) (lv : Nat) (depth : Nat) :
    Expr → List Expr → List Expr → CheckCM Bool
  | _, _, [] => pure true
  | ty, acc, arg :: rest => do
    match EO.stripTop (ty) with
    | .forallE _ dom body _ => do
        let dom' ← instListM dom acc
        let ta ← inferI eager lv false depth arg
        if ← defeqI eager lv depth ta dom' then
          iotaCertsFullIAux eager lv depth body (arg :: acc) rest
        else pure false
    | .bvar _ =>
      match acc with
      | [] => pure false
      | _ :: _ => do
        let ty' ← instListM ty acc
        iotaCertsFullIAux eager lv depth ty' [] (arg :: rest)
    | _ => pure false
termination_by _ acc args => (lv, 2, 2 * args.length + acc.length, 0)

/-- Twin of `iotaCertsFullI`. -/
def iotaCertsFullI (eager : Bool) (lv : Nat) (depth : Nat) (ty : Expr) (args : List Expr) : CheckCM Bool :=
  iotaCertsFullIAux eager lv depth ty [] args
termination_by (lv, 3, 0, 0)

/-- Twin of `defEqListI`. -/
def defEqListI (eager : Bool) (lv : Nat) (depth : Nat) : List Expr → List Expr → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← defeqI eager lv depth a b then defEqListI eager lv depth as bs else pure false
  | _, _ => pure false
termination_by as _ => (lv, 4, as.length, 0)

/-- Twin of `iotaIndexOkI`. -/
def iotaIndexOkI (eager : Bool) (lv : Nat) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) : CheckCM Bool :=
  if mI = rP then pure true
  else do
    match piResidual tyCtor margs with
    | some residual => defEqListI eager lv depth ((appArgs residual).drop cnP) idx
    | none => pure false
termination_by (lv, 5, 0, 0)

/-- Twin of `defeqSpineI`. -/
def defeqSpineI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  match a.getAppFnT with
  | .const n us =>
    match b.getAppFnT with
    | .const n' us' => do
      let aargs := appArgs a
      let bargs := appArgs b
      if n == n' ∧ aargs.length = bargs.length then
        match ← isEquivListLM us us' with
        -- last to first, as official `is_def_eq_args`
        | some true => defEqListI eager lv depth aargs.reverse bargs.reverse
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false
termination_by (lv, 6, 0, 0)

/-- Twin of `proofIrrelI`. -/
def proofIrrelI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  let ta ← inferI eager lv true depth a
  let tta ← inferI eager lv true depth ta
  let wtta ← whnfI eager lv depth tta
  match EO.stripTop (wtta) with
  | .sort uT => do
    let okA ← liftFueled "level comparison" (← isEquivLM uT .zero)
    let tb ← inferI eager lv true depth b
    let ttb ← inferI eager lv true depth tb
    let wttb ← whnfI eager lv depth ttb
    match EO.stripTop (wttb) with
    | .sort vT => do
      let okB ← liftFueled "level comparison" (← isEquivLM vT .zero)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false
termination_by (lv, 7, 0, 0)

/-- Twin of `propIrrelI`. -/
def propIrrelI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  if (← notProofFastM fe a) || (← notProofFastM fe b) then
    pure false
  else if (← isProofFastM fe a) && (← isProofFastM fe b) then
    pure true
  else proofIrrelI eager lv depth a b
termination_by (lv, 8, 0, 0)

/-- Twin of `structEtaCertWithI`. -/
def structEtaCertWithI (eager : Bool) (lv : Nat) (depth : Nat) (a b wtb : Expr) :
    CheckCM Bool := do
  match a.getAppFnT with
  | .const cn us => do
    match fe.ctorView? cn with
    | some (cvc, cnP, cnF, _) => do
      let aargs := appArgs a
      if aargs.length = cnP + cnF then
        match wtb.getAppFnT with
        | .const Tn us' => do
          match fe.indView? Tn with
          | some (cvT, caps) => do
            match fe.findTable? Tn with
            | some tbl => do
              let targs := appArgs wtb
              if caps.eta = true ∧ tbl.ctor == cn ∧
                  targs.length = tbl.numParams ∧
                  us'.length = cvT.levelParams.length ∧
                  cvc.levelParams == cvT.levelParams then do
                if ← liftFueled "level comparison" (← isEquivListLM us us') then do
                  if ← defEqListI eager lv depth (aargs.take tbl.numParams) targs then
                    defEqListI eager lv depth (aargs.drop tbl.numParams)
                      (projNodesI Tn b (List.range tbl.numFields))
                  else pure false
                else pure false
              else pure false
            | none => pure false
          | none => pure false
        | _ => pure false
      else pure false
    | none => pure false
  | _ => pure false
termination_by (lv, 9, 0, 0)

/-- Twin of `structEtaFullI`. -/
def structEtaFullI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  if etaCtorShapeC fe a then
    let tb ← inferI eager lv true depth b
    let wtb ← whnfI eager lv depth tb
    structEtaCertWithI eager lv depth a b wtb
  else pure false
termination_by (lv, 10, 0, 0)

/-- Twin of `structEtaExpandI`. -/
def structEtaExpandI (eager : Bool) (lv : Nat) :
    Nat → Nat → Expr → Expr → Expr → CheckCM Bool
  | 0, depth, a, b, _ => structEtaFullI eager lv depth a b
  | k + 1, depth, a, b, t =>
    match EO.stripTop t with
    | .forallE _ dom body _ => do
      let fv ← mkFVarM depth dom
      structEtaExpandI eager lv k (depth + 1) (.app a fv) (.app b fv) (body.inst1I fv)
    | _ => pure false
termination_by k _ _ _ _ => (lv, 11, k, 0)

/-- Twin of `structEtaCertI`. -/
def structEtaCertI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  if etaCtorShapeC fe a then structEtaFullI eager lv depth a b else
  match etaCtorPartialC fe a with
  | some k =>
    if !(Expr.ioNeutral b) then pure false else
    let ta ← inferI eager lv true depth a
    let tb ← inferI eager lv true depth b
    if ← defeqI eager lv depth tb ta then structEtaExpandI eager lv k depth a b ta
    else pure false
  | none => pure false
termination_by (lv, 12, 0, 0)

/-- Twin of `isPropTypeI`. -/
def isPropTypeI (eager : Bool) (lv : Nat) (depth : Nat) (T : Expr) : CheckCM Bool := do
  let tt ← inferI eager lv true depth T
  let w ← whnfI eager lv depth tt
  match EO.stripTop w with
  | .sort u => liftFueled "level comparison" (← isEquivLM u .zero)
  | _ => pure false
termination_by (lv, 13, 0, 0)

/-- Twin of `unitLikeFieldsI`. -/
def unitLikeFieldsI (eager : Bool) (lv : Nat) (ulf : Nat) :
    Nat → Nat → Expr → CheckCM Bool
  | 0, _, _ => pure true
  | n + 1, depth, t =>
    match EO.stripTop t with
    | .forallE _ dom body _ => do
      if ← isPropTypeI eager lv depth dom then do
        let fv ← mkFVarM depth dom
        unitLikeFieldsI eager lv ulf n (depth + 1) (body.inst1I fv)
      else if ← unitLikeLoopI eager lv ulf depth dom then do
        let fv ← mkFVarM depth dom
        unitLikeFieldsI eager lv ulf n (depth + 1) (body.inst1I fv)
      else pure false
    | _ => pure false
termination_by n _ _ => (lv, 16, 2 * ulf, n + 1)

/-- Twin of `unitLikeStructI`. -/
def unitLikeStructI (eager : Bool) (lv : Nat) (ulf : Nat)
    (depth : Nat) (w : Expr) : CheckCM Bool := do
  match ← unitLikeShapeM fe w with
  | some (tele, n) => unitLikeFieldsI eager lv ulf n depth tele
  | none => pure false
termination_by (lv, 16, 2 * ulf + 1, 0)

/-- Twin of `unitLikeLoopI`. -/
def unitLikeLoopI (eager : Bool) (lv : Nat) : Nat → Nat → Expr → CheckCM Bool
  | 0, _, _ => pure false
  | fuel + 1, depth, T => do
    let w ← whnfI eager lv depth T
    match EO.stripTop w with
    | .forallE _ dom body _ => do
      let fv ← mkFVarM depth dom
      unitLikeLoopI eager lv fuel (depth + 1) (body.inst1I fv)
    | _ => unitLikeStructI eager lv fuel depth w
termination_by f _ _ => (lv, 16, 2 * f, 0)

/-- Twin of `structUnitCertI`. -/
def structUnitCertI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  let ta ← inferI eager lv true depth a
  let wta ← whnfI eager lv depth ta
  if (EO.stripTop wta).isForall && !(Expr.ioNeutral a) then pure false else
  if ← unitLikeLoopI eager lv unitLikeFuel depth wta then
    let tb ← inferI eager lv true depth b
    let wtb ← whnfI eager lv depth tb
    if (EO.stripTop wtb).isForall && !(Expr.ioNeutral b) then pure false else
    defeqI eager lv depth wta wtb
  else pure false
termination_by (lv, 17, 0, 0)

/-- Twin of `etaCertI`. -/
def etaCertI (eager : Bool) (lv : Nat) (depth : Nat) (ty₁ body₁ : Expr) (b : Expr) : CheckCM Bool := do
  if !(Expr.ioNeutral b) then pure false else
  let tb ← inferI eager lv true depth b
  match EO.stripTop (← whnfI eager lv depth tb) with
  | .forallE _ ty₂ cod₂ _ => do
    if ← defeqI eager lv depth ty₂ ty₁ then do
      let fv ← mkFVarM depth ty₁
      let b₁ := body₁.inst1I fv
      unless ← defeqI eager lv (depth + 1) b₁ (.app b fv) do return false
      if mode.verifiedChecks then do
        let t₁ ← inferI eager lv false (depth + 1) b₁
        unless ← defeqI eager lv (depth + 1) t₁ (cod₂.inst1I fv) do return false
      pure true
    else pure false
  | _ => pure false
termination_by (lv, 18, 0, 0)

/-- Twin of `stuckIrrelI`. -/
def stuckIrrelI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool := do
  if ← structEtaCertI eager lv depth a b then pure true
  else if ← structEtaCertI eager lv depth b a then pure true
  else if ← structUnitCertI eager lv depth a b then pure true
  else proofIrrelI eager lv depth a b
termination_by (lv, 19, 0, 0)

/-- Twin of `formerSortLoopI`. -/
def formerSortLoopI (eager : Bool) (lv : Nat) : Nat → Nat → Expr → CheckCM (Option Level)
  | d, 0, e => do
    match EO.stripTop (← whnfI eager lv d e) with
    | .sort s => pure (some s)
    | _ => pure none
  | d, n + 1, e => do
    match EO.stripTop (← whnfI eager lv d e) with
    | .forallE _ dom b _ => do
      let fv ← mkFVarM d dom
      formerSortLoopI eager lv (d + 1) n (b.inst1I fv)
    | _ => pure none
termination_by _ n _ => (lv, 20, n, 0)

/-- Twin of `formerNeverZeroI`. -/
def formerNeverZeroI (eager : Bool) (lv : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) : CheckCM Bool :=
  match formerResSort cvT.type with
  | some _ => pure (formerNeverZero cvT us)
  | none => do
    let ty ← instLevelParamsM cvT.levelParams us cvT.type
    match ← formerSortLoopI eager lv 0 (caps.nparams + caps.nIdx) ty with
    | some s => pure (Lvl.zeronessOf s).isNever
    | none => pure false
termination_by (lv, 21, 0, 0)

/-- Twin of `familyNeverZeroI`. -/
def familyNeverZeroI (eager : Bool) (lv : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) : CheckCM Bool :=
  if caps.neverZero then pure true else formerNeverZeroI eager lv cvT caps us
termination_by (lv, 21, 1, 0)

/-- Twin of `iotaCase3I`. -/
def iotaCase3I (eager : Bool) (lv : Nat) (isK : Bool)
    (induct : Name) (us : List Level) : CheckCM Bool :=
  if isK then pure false else
  match ctorFamily fe induct with
  | some (cvT, caps) =>
    if cvT.levelParams.length == us.length then do
      let nz ← formerNeverZeroI eager lv cvT caps us
      pure !nz
    else pure true
  | none => pure true
termination_by (lv, 22, 0, 0)

/-- Twin of `majorToCtorI`. -/
def majorToCtorI (eager : Bool) (lv : Nat) (depth : Nat) (isK : Bool)
    (rules : List RecursorRule) (major : Expr) : CheckCM Expr := do
  if isCtorAppC fe major then pure major else
  match rules with
  | [rl] =>
    match fe.ctorView? rl.ctor with
    | some (cvj, cnP, _, T) =>
      match fe.indView? T with
      | some (cvT, caps) =>
        if isK = true then do
          let tmaj ← whnfI eager lv depth (← inferI eager lv true depth major)
          match tmaj.getAppFnT with
          | .const T' ust =>
            if T' == T ∧ cvj.levelParams.length = ust.length then do
              let margs := appArgs tmaj
              if cnP ≤ margs.length then do
                let fab ← mkAppNM (.const rl.ctor ust) (margs.take cnP)
                if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then do
                  -- official `to_cnstr_when_K`'s type check, both modes; the
                  -- proof-irrelevance certificate at the verified mode
                  let tfab ← inferI eager lv true depth fab
                  if ← defeqI eager lv depth tmaj tfab then
                    if ← certAtI mode (proofIrrelI eager lv depth fab major) then pure fab
                    else pure major
                  else pure major
                else pure major
              else pure major
            else pure major
          | _ => pure major
        else match etaRescueTable? (fe.findTable? T) rl.ctor cvj cvT caps with
        | some tbl => do
          let tmaj ← whnfI eager lv depth (← inferI eager lv true depth major)
          match tmaj.getAppFnT with
          | .const T' ust => do
            let margs := appArgs tmaj
            -- the counts are the table's
            if T' == T ∧ margs.length = tbl.numParams ∧
                ust.length = cvT.levelParams.length then do
              if ← familyNeverZeroI eager lv cvT caps ust then do
                let fab ← mkAppNM (.const tbl.ctor ust)
                  (margs ++ projNodesI T major (List.range tbl.numFields))
                if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then
                  pure fab
                else pure major
              else pure major
            else pure major
          | _ => pure major
        | none =>
          if T == andName then do
            let tmaj ← whnfI eager lv depth (← inferI eager lv true depth major)
            match tmaj.getAppFnT with
            | .const T' ust => do
              let margs := appArgs tmaj
              if T' == T ∧ margs.length = cnP ∧
                  cvj.levelParams.length = ust.length ∧
                  fe.andRescueSlotsF rl.ctor cnP = true then do
                let fab ← mkAppNM (.const rl.ctor ust) (margs ++ projNodesI T major [0, 1])
                if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then do
                  let tfab ← inferI eager lv true depth fab
                  if ← defeqI eager lv depth tmaj tfab then
                    if ← certAtI mode (proofIrrelI eager lv depth fab major) then pure fab
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else pure major
      | none => pure major
    | none => pure major
  | _ => pure major
termination_by (lv, 23, 0, 0)

/-- Twin of `litMajorToCtorI`. -/
def litMajorToCtorI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) : CheckCM Expr := do
  match EO.stripTop (e) with
  | .lit (.strVal s) =>
    if fe.strLit then whnfI eager lv depth (strLitToConstructor s)
    else pure e
  | _ => litToCtorIfNatI fe e
termination_by (lv, 24, 0, 0)

/-- Twin of `projLitToCtorI`. -/
def projLitToCtorI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) : CheckCM Expr := do
  match EO.stripTop (e) with
  | .lit (.strVal s) =>
    if fe.strLit then whnfI eager lv depth (strLitToConstructor s)
    else pure e
  | _ => pure e
termination_by (lv, 25, 0, 0)

/-- Twin of `prepareMajorI`. -/
def prepareMajorI (eager : Bool) (lv : Nat) (depth : Nat) (isK : Bool)
    (rules : List RecursorRule) (major : Expr) : CheckCM Expr := do
  if isK then do
    let majorK ← majorToCtorI eager lv depth isK rules major
    if isCtorAppC fe majorK then litMajorToCtorI eager lv depth majorK
    else pure majorK
  else do
    let majorE ← if (Expr.isStrLitI major) then pure major
      else majorToCtorI eager lv depth isK rules major
    if isCtorAppC fe majorE then pure majorE
    else do
      let major₀ ← whnfI eager lv depth majorE
      let major₁ ← litMajorToCtorI eager lv depth major₀
      majorToCtorI eager lv depth isK rules major₁
termination_by (lv, 26, 0, 0)

/-- Twin of `iotaRecI`, on the argument array `args` of a spine headed by
`h`: the ι step at the redex `h args[0:k]`.  Nothing of the redex is
rebuilt: the reduct is the rule's right-hand side applied to two ranges,
the recursor's leading arguments and the constructor's fields.  The rule's
firing mode is read only inside the certificate (`recFireAt`); the case
split reads the stored facts first (`iotaNoCert`), and the case-3
certificates read lists, built only there. -/
def iotaRecI (eager : Bool) (lv : Nat) (depth : Nat) (h : Expr) (args : Array Expr) (k : Nat) :
    CheckCM (Option Expr) := do
  match h with
  | .const c us => do
    match fe.recAt? c with
    | some (rv, isQuot) => do
      let mI := majorIdxOf rv
      let rP := rulePrefixOf rv
      if k = mI + 1 ∧ k ≤ args.size ∧ us.length = rv.levelParams.length ∧
          (peelPis (mI + 1) rv.type).isSome = true then do
        let major ← prepareMajorI eager lv depth rv.k rv.rules (spineArg args mI)
        match major.getAppFnT with
        | .const cj usj => do
          match fe.ctorView? cj with
          | some (cvj, cnP, _, induct) =>
            match rv.rules.find? (fun r' => r'.ctor == cj) with
            | some rl => do
              let margs := getAppArgsArr major
              if margs.size = cnP + rl.nfields then do
                if ← certAtI mode (do
                    let fire := recFireAt rv isQuot
                    -- case 2 by the stored facts: no comparand is computed
                    if iotaNoCert fe rv.k induct (recFireLevelCount fire cvj.levelParams) then
                      pure true
                    else do
                    let cmpLvls : List Level ←
                      match fire with
                      | .nested lvls _ => substLevelTreesM rv.levelParams us lvls
                      | .plain =>
                        substLevelTreesM rv.levelParams us (cvj.levelParams.map Level.param)
                      | .levels lvls => substLevelTreesM rv.levelParams us lvls
                    if ← iotaCase3I eager lv rv.k induct cmpLvls then do
                      if ← liftFueled "level comparison" (← isEquivListLM usj cmpLvls) then do
                        let argsL := args.toList.take k
                        let margsL := margs.toList
                        let cmpArgs : List Expr ←
                          match fire with
                          | .nested _ pins =>
                            match pinArgsI rv.levelParams us (argsL.take rP) pins with
                            | some ps => pure ps
                            | none => throw (.internal "universe level too deep")
                          | .plain => pure (argsL.take cnP)
                          | .levels _ => pure (argsL.take cnP)
                        if ← defEqListI eager lv depth (margsL.take cnP) cmpArgs then do
                          let tyCtor ← constTyAtM fe cj usj
                          if ← iotaCertsFullI eager lv depth tyCtor margsL then
                            iotaIndexOkI eager lv depth mI rP cnP tyCtor margsL
                              ((argsL.take mI).drop rP)
                          else pure false
                        else pure false
                      else pure false
                    else pure true) then do
                  let rhs ← ruleRhsAtM fe c cj us
                  pure (some (mkAppRange (mkAppRange rhs args 0 (min rP k)) margs cnP margs.size))
                else pure none
              else pure none
            | none => pure none
          | none => pure none
        | _ => pure none
      else pure none
    | none => pure none
  | _ => pure none
termination_by (lv, 27, 0, 0)

/-- Twin of `reduceProjCoreI`. -/
def reduceProjCoreI (eager : Bool) (lv : Nat) (depth : Nat) (sn : Name) (i : Nat) (c : Expr) :
    CheckCM (Option Expr) := do
  let e' ← projLitToCtorI eager lv depth c
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
termination_by (lv, 28, 0, 0)

/-- Twin of `betaPeelI`: `t` is the raw lambda body past the binders
consumed so far, `acc` their arguments (innermost first), `args[i:]` the
spine left.  The body is substituted once, when peeling stops, without a
memo (Lean's `instantiate`, not `instListM`: official's `instantiate` keeps
no cache across calls), and applied to the arguments left over. -/
def betaPeelI (eager : Bool) (lv : Nat) (depth : Nat)
    (t : Expr) (acc : List Expr) (args : Array Expr) (i : Nat) : CheckCM WhnfStep :=
  if hi : i < args.size then
    match EO.stripTop (t) with
    | .lam _ _ body _ => betaPeelI eager lv depth body (args[i] :: acc) args (i + 1)
    | _ => pure (.cont (mkAppRange (t.instI acc.toArray) args i args.size))
  else pure (.cont (t.instI acc.toArray))
termination_by (lv, 29, args.size - i, 0)

/-- Twin of `whnfAppI`, over the spine `args[i:]`; a ι step is reported to the
poll (`Event.unfold`). -/
def whnfAppI (eager : Bool) (lv : Nat) (depth : Nat)
    (v : Expr) (args : Array Expr) (i : Nat) : CheckCM WhnfStep :=
  if hi : i < args.size then
    match EO.stripTop (v) with
    | .lam _ _ body _ => betaPeelI eager lv depth body [args[i]] args (i + 1)
    | _ => do
      let fa := Expr.app v args[i]
      match ← (if iotaArityOk fe fa then
                 iotaRecI eager lv depth fa.getAppFnT (getAppArgsArr fa) (iotaNumArgs fa 0)
               else pure none) with
      | some e'' =>
        pollC fe (.unfold (headConstName fa)) (pure (.cont (mkAppRange e'' args (i + 1) args.size)))
      | none => whnfAppI eager lv depth fa args (i + 1)
  else pure (.done v)
termination_by (lv, 30, args.size - i, 0)

/-- Twin of `whnfStuckI`: a spine `e` whose head `h` is its own head normal
form and not a lambda (official `whnf_core`'s `f == f0` arm): the ι step,
tried once, at the one prefix where it can fire (`iotaTargetF`), on the
spine's argument array, and otherwise the input itself, with nothing
rebuilt.  A ι step is reported to the poll (`Event.unfold`), as in
`whnfAppI`. -/
def whnfStuckI (eager : Bool) (lv : Nat) (depth : Nat) (h e : Expr) :
    CheckCM WhnfStep := do
  match iotaTargetF fe h with
  | some k =>
    if k ≤ iotaNumArgs e 0 then do
      let args := getAppArgsArr e
      match ← iotaRecI eager lv depth h args k with
      | some e'' =>
        pollC fe (.unfold (headConstName h)) (pure (.cont (mkAppRange e'' args k args.size)))
      | none => pure (.done e)
    else pure (.done e)
  | none => pure (.done e)
termination_by (lv, 30, 0, 0)

/-- Twin of `whnfCoreStepI`; `mdata` is looked through.  A spine whose
head is its own head normal form goes to `whnfStuckI`; `h` is the term's
spine head (`getAppFnT`), computed by the loop. -/
def whnfCoreStepI (eager : Bool) (lv : Nat) (cheap : Bool) (depth : Nat)
    (h e : Expr) : CheckCM WhnfStep := do
    match EO.stripTop (e) with
    | .sort _ | .fvar .. | .forallE .. | .lam .. | .const .. | .lit _ => pure (.done e)
    | .app _ _ => do
      -- a head that is its own head normal form: the spine is stuck but
      -- for ι, and is answered by itself
      if isStuckHeadC h then whnfStuckI eager lv depth h e
      else do
        let args := getAppArgsArr e
        let v ← whnfCoreI eager lv cheap depth h
        whnfAppI eager lv depth v args 0
    | .proj sn i pe => do
      let c ← if cheap then whnfCoreI eager lv true depth pe else whnfI eager lv depth pe
      match ← reduceProjCoreI eager lv depth sn i c with
      | some m' => pure (.cont m')
      | none => pure (.done e)
    | .letE _ _ v b _ => pure (.cont (b.inst1I v))
    | .mdata _ b => pure (.cont b)
    | .bvar _ | .mvar _ => throw (.notImplemented "whnf beyond the supported fragment")
termination_by (lv, 31, 0, 0)

/-- Twin of `whnfCoreLoopI`: `whnfCoreStepI` iterated on its own step
budget, with official `whnf_core`'s memo policy.  Every step looks its term
up (`whnfCoreKeyC`: a term no arm stores is not looked up), a hit ends the
chain, and the keys of the steps taken so far (`pend`; `pendC` those the
cheap mode takes alike, `whnfCoreCheapSafeC`) wait for the chain's answer,
stored at its end (`storeChainI`).  The cheap mode reads its own memo and
stores nothing. -/
def whnfCoreLoopI (eager : Bool) (lv : Nat) (cheap : Bool) (depth : Nat) :
    Nat → List Expr → List Expr → Expr → CheckCM Expr
  | 0, _, _, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, pend, pendC, e => do
    if whnfCoreEasy e then
      storeChainI cheap pend pendC e
      pure e
    else
      let h := e.getAppFnT
      let key := whnfCoreKeyC h e
      match ← (if key then whnfCoreLookupI cheap e else pure none) with
      | some r =>
        storeChainI cheap pend [] r
        pure r
      | none =>
        let safe := whnfCoreCheapSafeC h e
        match ← whnfCoreStepI eager lv cheap depth h e with
        | .done v =>
          let st := !cheap && whnfCoreStoresDone key e v
          storeChainI cheap (pushKey st e pend) (pushCheapKey safe st e pendC) v
          pure v
        | .cont e' =>
          let st := !cheap && key
          whnfCoreLoopI eager lv cheap depth n (pushKey st e pend) (pushCheapKey safe st e pendC) e'
termination_by n _ _ _ => (lv, 32, n, 0)

/-- Twin of `whnfCoreBodyI`: the loop with no key pending. -/
def whnfCoreBodyI (eager : Bool) (lv : Nat) : Bool → Nat → Expr → CheckCM Expr :=
  fun cheap depth e => whnfCoreLoopI eager lv cheap depth whnfCoreLoopFuel [] [] e
termination_by (lv, 33, 0, 0)

/-- Twin of `defeqArgI`: an `eagerReduce _ _` argument's type is compared
in the eager tower. -/
def defeqArgI (eager : Bool) (lv : Nat) (depth : Nat) (a ta ty : Expr) : CheckCM Bool :=
  if Expr.isEagerReduce a then defeqEI eager lv depth ta ty else defeqI eager lv depth ta ty
termination_by (lv, 34, 0, 0)

/-- Twin of `inferSpineI`. -/
def inferSpineI (eager : Bool) (lv : Nat) (io : Bool) (depth : Nat) : Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match EO.stripTop (ty) with
    | .forallE _ dom body _ => do
      let dom' ← instListRevM dom acc
      let ta ← inferI eager lv io depth a
      unless ← defeqArgI eager lv depth a ta dom' do
        throw (.invalid "application type mismatch")
      inferSpineI eager lv io depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      match EO.stripTop (← whnfI eager lv depth ty') with
      | .forallE _ dom body _ => do
        let ta ← inferI eager lv io depth a
        unless ← defeqArgI eager lv depth a ta dom do
          throw (.invalid "application type mismatch")
        inferSpineI eager lv io depth body #[a] rest
      | _ => throw (.invalid "function expected")
termination_by _ _ args => (lv, 35, args.length, 0)

/-- Twin of `inferSpineIOI`. -/
def inferSpineIOI (eager : Bool) (lv : Nat) (depth : Nat) : Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match EO.stripTop (ty) with
    | .forallE _ _ body _ => inferSpineIOI eager lv depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      match EO.stripTop (← whnfI eager lv depth ty') with
      | .forallE _ _ body _ => inferSpineIOI eager lv depth body #[a] rest
      | _ => throw (.invalid "function expected")
termination_by _ _ args => (lv, 36, args.length, 0)

/-- Twin of `whnfLoopI`, each step `whnfStep`'s: the continuation is the
loop's own tail call. -/
def whnfLoopI (eager : Bool) (lv : Nat) (depth : Nat) : Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => do
    let e₁ ← whnfCoreI eager lv false depth e
    match ← reduceNatI eager lv depth e₁ with
    -- a computed literal is the answer (official `whnf`); a `Bool`
    -- constructor goes on (see `whnfStep`)
    | some e₂ => if Expr.isLitI e₂ then pure e₂ else whnfLoopI eager lv depth n e₂
    | none =>
      match ← unfoldDefinitionI fe e₁ with
      | some e₂ => whnfLoopI eager lv depth n e₂
      | none => pure e₁
termination_by n _ => (lv, 37, n, 0)

/-- Twin of `whnfBodyI`. -/
def whnfBodyI (eager : Bool) (lv : Nat) : Nat → Expr → CheckCM Expr :=
  fun depth e => whnfLoopI eager lv depth whnfLoopFuel e
termination_by (lv, 38, 0, 0)

/-- Twin of `ensureSortI`. -/
def ensureSortI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) : CheckCM Level := do
  match EO.stripTop (← whnfI eager lv depth e) with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")
termination_by (lv, 39, 0, 0)

/-- Twin of `checkGuardRowsI`. -/
def checkGuardRowsI (eager : Bool) (lv : Nat) (guardSort : Level) :
    List (Nat × Expr) → CheckCM Unit
  | [] => pure ()
  | (d, dom) :: rest => do
    let t ← inferI eager lv true d dom
    match EO.stripTop (← whnfI eager lv d t) with
    | .sort u =>
      unless Lvl.zeroWhereZero guardSort u do
        throw (.invalid "projection from a propositional structure must be a proposition")
      checkGuardRowsI eager lv guardSort rest
    | _ => throw (.invalid "expected a sort")
termination_by rows => (lv, 40, rows.length, 0)

/-- Twin of `projGuardSortI`. -/
def projGuardSortI (eager : Bool) (lv : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) : CheckCM (Option Level) :=
  match formerResSort cvT.type with
  | some s => pure (if Lvl.isAlwaysZero s then some .zero else none)
  | none => do
    let ty ← instLevelParamsM cvT.levelParams us cvT.type
    match ← formerSortLoopI eager lv 0 (caps.nparams + caps.nIdx) ty with
    | some s => pure (if (Lvl.zeronessOf s).isNever then none else some s)
    | none => throw (.invalid "projection from a structure whose type reaches no sort")
termination_by (lv, 41, 0, 0)

/-- Twin of `checkProjRowsI`: the constructor's type at the use's levels, its
parameters opened with the field telescope left raw (`openPisRawM`); where no
field before the projected one is mentioned after it (`projGuardFast`), the
one row is the projected field's domain, its parameters substituted, and the
telescope is read, not rebuilt; otherwise the telescope is substituted and its
fields stepped (`projGuardRowsGoM`). -/
def checkProjRowsI (eager : Bool) (lv : Nat) (entry : ProjEntry)
    (us : List Level) (guardSort : Level) : CheckCM Unit := do
  match fe.find? entry.ctor with
  | some _ => do
    let cty ← constTyAtM fe entry.ctor us
    match ← openPisRawM #[] entry.numParams cty 0 with
    | some (acc, r) =>
      match projGuardFast entry.idx 0 r with
      | some dom =>
        checkGuardRowsI eager lv guardSort
          [(entry.numParams + entry.idx, EO.instantiateRevAt dom acc entry.idx)]
      | none =>
        match ← projGuardRowsGoM entry.idx entry.numParams (r.instRevI acc) with
        | some rows => checkGuardRowsI eager lv guardSort rows
        | none =>
          throw (.invalid "projection from a propositional structure must be a proposition")
    | none =>
      throw (.invalid "projection from a propositional structure must be a proposition")
  | none =>
    throw (.invalid "projection from a propositional structure must be a proposition")
termination_by (lv, 42, 0, 0)

/-- Twin of `checkProjGuardI`. -/
def checkProjGuardI (eager : Bool) (lv : Nat) (entry : ProjEntry)
    (us : List Level) : CheckCM Unit := do
  match fe.indView? entry.structName with
  | some (cvT, caps) => do
    match ← projGuardSortI eager lv cvT caps us with
    | none => pure ()
    | some guardSort => checkProjRowsI eager lv entry us guardSort
  | none => throw (.invalid "projection from a propositional structure must be a proposition")
termination_by (lv, 43, 0, 0)

/-- Twin of `inferLamsLeafI`. -/
def inferLamsLeafI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Expr) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← inferI eager lv io (d + k) ob
  let cur ← abstractRangeM bt d k
  inferLamsOutI d stk (k - 1) cur
termination_by (lv, 44, 0, 0)

/-- Twin of `inferLamsI`. -/
def inferLamsI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Expr → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match EO.stripTop (t) with
    | .lam _ ty body _ => do
      let tyo ← instListRevM ty fvs
      let tty ← inferI eager lv io (d + k) tyo
      match EO.stripTop (← whnfI eager lv (d + k) tty) with
      | .sort _ => do
        let fv ← mkFVarM (d + k) tyo
        inferLamsI eager lv io d fuel body (k + 1) (fvs.push fv) (tyo :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferLamsLeafI eager lv io d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeafI eager lv io d t k fvs stk
termination_by f _ _ _ _ => (lv, 45, f, 0)

/-- Twin of `inferPisLeafI`; an `imax` chain past C's depth bound is an
internal error (C's `Level.mkData` would abort). -/
def inferPisLeafI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Level) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← inferI eager lv io (d + k) ob
  match EO.stripTop (← whnfI eager lv (d + k) bt) with
  | .sort v =>
    if EO.imaxChainFits stk v then pure (.sort (inferPisOutI stk v))
    else throw (.internal "universe level too deep")
  | _ => throw (.invalid "expected a sort")
termination_by (lv, 46, 0, 0)

/-- Twin of `inferPisI`. -/
def inferPisI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Level → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match EO.stripTop (t) with
    | .forallE _ ty body _ => do
      let tyo ← instListRevM ty fvs
      let tty ← inferI eager lv io (d + k) tyo
      match EO.stripTop (← whnfI eager lv (d + k) tty) with
      | .sort u => do
        let fv ← mkFVarM (d + k) tyo
        inferPisI eager lv io d fuel body (k + 1) (fvs.push fv) (u :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferPisLeafI eager lv io d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeafI eager lv io d t k fvs stk
termination_by f _ _ _ _ => (lv, 47, f, 0)

/-- Twin of `inferBodyI`; a sort's successor past C's depth bound is an
internal error. -/
def inferBodyI (eager : Bool) (lv : Nat) (io : Bool) : Nat → Expr → CheckCM Expr :=
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
      if fe.natLit then do
        if natSizeBytes n > fe.limits.maxNatSize then throw (.invalid natTooBigMsg)
        pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if fe.strLit then pure (.const stringName [])
      else throw (.notImplemented "string literals before the String support declarations")
    | .forallE _ ty body _ => do
      let tty ← inferI eager lv io depth ty
      match EO.stripTop (← whnfI eager lv depth tty) with
      | .sort u => do
        let fv ← mkFVarM depth ty
        inferPisI eager lv io depth (← peelFuelM) body 1 #[fv] [u]
      | _ => throw (.invalid "expected a sort")
    | .lam _ ty body _ => do
      let tty ← inferI eager lv io depth ty
      match EO.stripTop (← whnfI eager lv depth tty) with
      | .sort _ => do
        let fv ← mkFVarM depth ty
        inferLamsI eager lv io depth (← peelFuelM) body 1 #[fv] [ty]
      | _ => throw (.invalid "expected a sort")
    | .app _ _ => do
      let tf ← inferI eager lv io depth e.getAppFnT
      inferSpineI eager lv io depth tf #[] (appArgs e)
    | .proj sn i pe => do
      let tpe ← inferI eager lv io depth pe
      let te ← whnfI eager lv depth tpe
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
            checkProjGuardI eager lv entry us
            match entry.typeAtI us targs pe with
            | some ty => pure ty
            | none => throw (.internal "projection body unreadable")
          else throw (.notImplemented "projection without a native entry")
        | none =>
          throw (projMissError fe (fe.hasTable T) T sn i (appArgs te).length)
      | _ => throw (.invalid "invalid projection: not a structure-like type, or no such field")
    | .letE _ ty v b _ => do
      let tty ← inferI eager lv io depth ty
      let _ ← ensureSortI eager lv depth tty
      let tv ← inferI eager lv io depth v
      unless ← defeqI eager lv depth tv ty do
        throw (.invalid "let value type mismatch")
      inferI eager lv io depth (b.inst1I v)
    | .mdata _ b => inferI eager lv io depth b
    | .bvar _ | .mvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")
termination_by (lv, 48, 0, 0)

/-- Twin of `inferBodyIOI`; an `imax` past C's depth bound is an internal
error. -/
def inferBodyIOI (eager : Bool) (lv : Nat) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match EO.stripTop (e) with
    | .app _ _ => do
      let tf ← inferI eager lv true depth e.getAppFnT
      inferSpineIOI eager lv depth tf #[] (appArgs e)
    | .forallE _ ty body _ => do
      let tty ← inferI eager lv true depth ty
      match EO.stripTop (← whnfI eager lv depth tty) with
      | .sort u => do
        let fv ← mkFVarM depth ty
        let bt ← inferI eager lv true (depth + 1) (body.inst1I fv)
        let v ← ensureSortI eager lv (depth + 1) bt
        if EO.imaxChainFits [u] v then pure (.sort (.imax u v))
        else throw (.internal "universe level too deep")
      | _ => throw (.invalid "expected a sort")
    | .lam _ ty body _ => do
      let fv ← mkFVarM depth ty
      let bt ← inferI eager lv true (depth + 1) (body.inst1I fv)
      let bAbs ← abstract1M bt depth
      pure (.forallE .anonymous ty bAbs .default)
    | .letE _ _ v b _ => inferI eager lv true depth (b.inst1I v)
    | .mdata _ b => inferI eager lv true depth b
    | _ => inferBodyI eager lv true depth e
termination_by (lv, 49, 0, 0)

/-- Twin of `boolTrueShortcutI`. -/
def boolTrueShortcutI (eager : Bool) (lv : Nat) (depth : Nat) (a : Expr) : CheckCM Bool := do
  pure (Expr.isBoolTrue (← whnfI eager lv depth a))
termination_by (lv, 50, 0, 0)

/-- Twin of `defeqBindersInnerI`. -/
def defeqBindersInnerI (eager : Bool) (lv : Nat) (lam : Bool) (depth : Nat) (b₁ b₂ : Expr) :
    CheckCM Bool := do
  unless ← defeqI eager lv (depth + 1) b₁ b₂ do return false
  if lam && mode.verifiedChecks then do
    let t₁ ← inferI eager lv false (depth + 1) b₁
    let t₂ ← inferI eager lv false (depth + 1) b₂
    unless ← defeqI eager lv (depth + 1) t₁ t₂ do return false
  pure true
termination_by (lv, 51, 0, 0)

/-- Twin of `defeqDomainI`. -/
def defeqDomainI (eager : Bool) (lv : Nat) (depth : Nat) (fvs : Array Expr) (ty₁ ty₂ dom₂ : Expr) :
    CheckCM Bool :=
  if ty₁ == ty₂ then pure true else do
    let dom₁ ← instListRevM ty₁ fvs
    defeqI eager lv depth dom₁ dom₂
termination_by (lv, 52, 0, 0)

/-- Twin of `defeqBindersI` (the official `is_def_eq_binding`): the
variables so far are an `Array`, outermost first, so that each opening is
one `instantiateRev` walk over it. -/
def defeqBindersI (eager : Bool) (lv : Nat) (lam : Bool) :
    Nat → Nat → Array Expr → Expr → Expr → Expr → Expr → CheckCM Bool
  | fuel, depth, fvs, ty₁, body₁, ty₂, body₂ => do
    let dom₂ ← instListRevM ty₂ fvs
    unless ← defeqDomainI eager lv depth fvs ty₁ ty₂ dom₂ do return false
    let fv ← mkFVarM depth dom₂
    let fvs' ← pure (fvs.push fv)
    match fuel, Expr.binderPair? lam body₁ body₂ with
    | fuel + 1, some (ty₁', body₁', ty₂', body₂') =>
      defeqBindersI eager lv lam fuel (depth + 1) fvs' ty₁' body₁' ty₂' body₂'
    | _, _ => do
      let b₁ ← instListRevM body₁ fvs'
      let b₂ ← instListRevM body₂ fvs'
      defeqBindersInnerI eager lv lam depth b₁ b₂
termination_by f _ _ _ _ _ _ => (lv, 53, f, 0)

/-- Twin of `quickDefEqI`. -/
def quickDefEqI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM (Option Bool) :=
  if a == b then pure (some true) else
  match EO.stripTop a, EO.stripTop b with
  | .sort u, .sort v => do pure (some (← liftFueled "level comparison" (← isEquivLM u v)))
  | .lit l₁, .lit l₂ => pure (some (Literal.beqI l₁ l₂))
  | .forallE _ ty₁ body₁ _, .forallE _ ty₂ body₂ _ => do
    let ok ← defeqBindersI eager lv false bindersFuel depth #[] ty₁ body₁ ty₂ body₂
    pure (some ok)
  | .lam _ ty₁ body₁ _, .lam _ ty₂ body₂ _ => do
    let ok ← defeqBindersI eager lv true bindersFuel depth #[] ty₁ body₁ ty₂ body₂
    pure (some ok)
  | _, _ => pure none
termination_by (lv, 54, 0, 0)

/-- Twin of `defeqOffsetI`. -/
def defeqOffsetI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM (Option Bool) :=
  if (Expr.isNatZero a) && (Expr.isNatZero b) then pure (some true) else
  if (Expr.isLitI a) && (Expr.isLitI b) then pure none else
  match (Expr.natPred? a), (Expr.natPred? b) with
  | some x, some y => do pure (some (← defeqI eager lv depth x y))
  | _, _ => pure none
termination_by (lv, 55, 0, 0)

/-- Twin of `tryUnfoldProjAppI`. -/
def tryUnfoldProjAppI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) : CheckCM (Option Expr) :=
  if Expr.headIsProj e then do
    let e' ← whnfCoreI eager lv false depth e
    if e' == e then pure none else pure (some e')
  else pure none
termination_by (lv, 56, 0, 0)

/-- Twin of `deltaQuickI`. -/
def deltaQuickI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM DeltaStep := do
  match ← quickDefEqI eager lv depth a b with
  | some true => pure .eq
  | some false => pure .diff
  | none => pure (.cont a b)
termination_by (lv, 57, 0, 0)

/-- Twin of `lazyDeltaStepI`. -/
def lazyDeltaStepI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM DeltaStep := do
  match unfoldableHeadC fe a, unfoldableHeadC fe b with
  | false, false => pure .unknown
  | true, false =>
    match ← tryUnfoldProjAppI eager lv depth b with
    | some b₂ => deltaQuickI eager lv depth a b₂
    | none =>
      match ← unfoldDefinitionI fe a with
      | some a₂ => deltaQuickI eager lv depth (← whnfCoreI eager lv true depth a₂) b
      | none => pure .unknown
  | false, true =>
    match ← tryUnfoldProjAppI eager lv depth a with
    | some a₂ => deltaQuickI eager lv depth a₂ b
    | none =>
      match ← unfoldDefinitionI fe b with
      | some b₂ => deltaQuickI eager lv depth a (← whnfCoreI eager lv true depth b₂)
      | none => pure .unknown
  | true, true => do
    let ha := headHintC fe a
    let hb := headHintC fe b
    if hintLt hb ha then
      match ← unfoldDefinitionI fe a with
      | some a₂ => deltaQuickI eager lv depth (← whnfCoreI eager lv true depth a₂) b
      | none => pure .unknown
    else if hintLt ha hb then
      match ← unfoldDefinitionI fe b with
      | some b₂ => deltaQuickI eager lv depth a (← whnfCoreI eager lv true depth b₂)
      | none => pure .unknown
    else if ← (if hintSameRegular ha hb && sameConstHeadsC a b then
        defeqSpineI eager lv depth a b else pure false) then pure .eq
    else
      match ← unfoldDefinitionI fe a, ← unfoldDefinitionI fe b with
      | some a₂, some b₂ => do
        let a₃ ← whnfCoreI eager lv true depth a₂
        let b₃ ← whnfCoreI eager lv true depth b₂
        deltaQuickI eager lv depth a₃ b₃
      | _, _ => pure .unknown
termination_by (lv, 58, 0, 0)

/-- Twin of `lazyDeltaReductionI`. -/
def lazyDeltaReductionI (eager : Bool) (lv : Nat) (depth : Nat) :
    Nat → Expr → Expr → CheckCM LazyRes
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | n + 1, a, b => do
    match ← defeqOffsetI eager lv depth a b with
    | some v => pure (.verdict v)
    | none =>
    -- the eager flag folds with free variables present
    let fold := eager || (!a.hasFVar && !b.hasFVar)
    match ← (if fold then reduceNatI eager lv depth a else pure none) with
    | some a₂ => pure (.verdict (← defeqI eager lv depth a₂ b))
    | none =>
    match ← (if fold then reduceNatI eager lv depth b else pure none) with
    | some b₂ => pure (.verdict (← defeqI eager lv depth a b₂))
    | none =>
    match ← lazyDeltaStepI eager lv depth a b with
    | .cont a' b' => lazyDeltaReductionI eager lv depth n a' b'
    | .eq => pure (.verdict true)
    | .diff => pure (.verdict false)
    | .unknown => pure (.unknown a b)
termination_by n _ _ => (lv, 59, n, 0)

/-- Twin of `lazyDeltaProjReductionI`. -/
def lazyDeltaProjReductionI (eager : Bool) (lv : Nat) (depth : Nat) (sn : Name) (i : Nat) :
    Nat → Expr → Expr → CheckCM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: lazy delta projection loop")
  | n + 1, a, b => do
    match ← lazyDeltaStepI eager lv depth a b with
    | .cont a' b' => lazyDeltaProjReductionI eager lv depth sn i n a' b'
    | .eq => pure true
    | .diff | .unknown =>
      match ← reduceProjCoreI eager lv depth sn i a with
      | some x =>
        match ← reduceProjCoreI eager lv depth sn i b with
        | some y => defeqI eager lv depth x y
        | none => defeqI eager lv depth a b
      | none => defeqI eager lv depth a b
termination_by n _ _ => (lv, 60, n, 0)

/-- Twin of `defeqProjPairI`. -/
def defeqProjPairI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool :=
  match EO.stripTop a, EO.stripTop b with
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
    if s₁ == s₂ && i₁ == i₂ then
      lazyDeltaProjReductionI eager lv depth s₁ i₁ defeqLoopFuel e₁ e₂
    else pure false
  | _, _ => pure false
termination_by (lv, 61, 0, 0)

/-- Twin of `defeqStuckI`; two free variables are compared by depth, as
con-leche compares its levels. -/
def defeqStuckI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM Bool :=
  match EO.stripTop a, EO.stripTop b with
  | .lit l, .app fO _ => do
    match l, EO.stripTop fO with
    | .strVal s, .const cO usO =>
      if cO == stringOfListName ∧ usO = [] ∧ fe.strLit then
        defeqI eager lv depth (strLitToConstructor s) b
      else stuckIrrelI eager lv depth a b
    | _, _ => stuckIrrelI eager lv depth a b
  | .app fO _, .lit l => do
    match l, EO.stripTop fO with
    | .strVal s, .const cO usO =>
      if cO == stringOfListName ∧ usO = [] ∧ fe.strLit then
        defeqI eager lv depth a (strLitToConstructor s)
      else stuckIrrelI eager lv depth a b
    | _, _ => stuckIrrelI eager lv depth a b
  | .fvar i, .fvar j =>
    if fvarDepth? i == fvarDepth? j then pure true
    else stuckIrrelI eager lv depth a b
  | .const n us, .const n' us' =>
    if n == n' then do
      if ← liftFueled "level comparison" (← isEquivListLM us us') then pure true
      else stuckIrrelI eager lv depth a b
    else stuckIrrelI eager lv depth a b
  | .app .., .app .. => do
    let as₁ := appArgs a
    let as₂ := appArgs b
    if as₁.length = as₂.length then do
      if ← defeqI eager lv depth a.getAppFnT b.getAppFnT then do
        if ← defEqListI eager lv depth as₁ as₂ then pure true
        else stuckIrrelI eager lv depth a b
      else stuckIrrelI eager lv depth a b
    else stuckIrrelI eager lv depth a b
  | .lam _ ty₁ body₁ _, _ => do
    if ← etaCertI eager lv depth ty₁ body₁ b then pure true
    else stuckIrrelI eager lv depth a b
  | _, .lam _ ty₂ body₂ _ => do
    if ← etaCertI eager lv depth ty₂ body₂ a then pure true
    else stuckIrrelI eager lv depth a b
  | _, _ => stuckIrrelI eager lv depth a b
termination_by (lv, 62, 0, 0)

/-- Twin of `defeqBodyI`. -/
def defeqBodyI (eager : Bool) (lv : Nat) : Nat → Expr → Expr → CheckCM Bool :=
  fun depth a b => do
    if a == b then pure true else
    -- the eq-true shortcut
    if ← (if Expr.isBoolTrue b && (eager || !a.hasFVar) then boolTrueShortcutI eager lv depth a
        else pure false) then pure true else
    match ← quickDefEqI eager lv depth a b with
    | some v => pure v
    | none =>
    -- proof irrelevance before any head normalisation
    if ← propIrrelI eager lv depth a b then pure true else
    let a' ← whnfCoreI eager lv true depth a
    let b' ← whnfCoreI eager lv true depth b
    match ← quickDefEqI eager lv depth a' b' with
    | some v => pure v
    | none =>
    match ← lazyDeltaReductionI eager lv depth defeqLoopFuel a' b' with
    | .verdict v => pure v
    | .unknown a₁ b₁ =>
    if ← defeqProjPairI eager lv depth a₁ b₁ then pure true else
    if !(Expr.headIsProj a₁) && !(Expr.headIsProj b₁) then
      defeqStuckI eager lv depth a₁ b₁ else
    let a₂ ← whnfCoreI eager lv false depth a₁
    let b₂ ← whnfCoreI eager lv false depth b₁
    if a₂ == a₁ && b₂ == b₁ then defeqStuckI eager lv depth a₁ b₁
    else defeqI eager lv depth a₂ b₂
termination_by (lv, 63, 0, 0)


/-- Twin of the `whnfCore` entry point: the loop, which looks its terms up in
the mode's memo (`whnfCoreLoopI`).  An easy case (`whnfCoreEasy`) returns
at once, as the loop's first step would; any other term runs the loop behind
the poll. -/
def whnfCoreI (eager : Bool) : Nat → Bool → Nat → Expr → CheckCM Expr
  | 0, _, _, _ => throw (.limit .recDepth)
  | lv + 1, c, d, e =>
    if whnfCoreEasy e then pure e
    else pollC fe (.body d) (whnfCoreBodyI eager lv c d e)
termination_by lv _ _ _ => (lv, 0, 0, 0)

/-- Twin of the `whnf` entry point; its easy cases (`whnfEasy`) return
before the memo, as official. -/
def whnfI (eager : Bool) : Nat → Nat → Expr → CheckCM Expr
  | 0, _, _ => throw (.limit .recDepth)
  | lv + 1, d, e =>
    if whnfEasy e then pure e
    else memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
      (fun d e => pollC fe (.body d) (whnfBodyI eager lv d e)) d e
termination_by lv _ _ => (lv, 0, 0, 0)

/-- Twin of the inference entry point, at the full grade (`io := false`)
or at the io grade (`io := true`, official `infer_only`), each under its
own memo. -/
def inferI (eager : Bool) : Nat → Bool → Nat → Expr → CheckCM Expr
  | 0, _, _, _ => throw (.limit .recDepth)
  | lv + 1, io, d, e =>
    if io then
      memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
        (fun d e => pollC fe (.body d) (inferBodyIOI eager lv d e)) d e
    else memoEI (·.inferC) (fun st mp => { st with inferC := mp })
      (fun d e => pollC fe (.body d) (inferBodyI eager lv false d e)) d e
termination_by lv _ _ _ => (lv, 0, 0, 0)

/-- Twin of the definitional-equality entry point, in the tower `eager`. -/
def defeqI (eager : Bool) : Nat → Nat → Expr → Expr → CheckCM Bool
  | 0, _, _, _ => throw (.limit .recDepth)
  | lv + 1, d, a, b =>
    memoBI (fun d a b => pollC fe (.body d) (defeqBodyI eager lv d a b)) d a b
termination_by lv _ _ _ => (lv, 0, 0, 0)

/-- Twin of the eager entry point: the comparison in the eager tower (the
bodies at `eager := true` one level down) on its own memos
(`withEagerMemos`). -/
def defeqEI (eager : Bool) : Nat → Nat → Expr → Expr → CheckCM Bool
  | 0, _, _, _ => throw (.limit .recDepth)
  | lv + 1, d, a, b =>
    withEagerMemos eager
      (memoBI (fun d a b => pollC fe (.body d) (defeqBodyI true lv d a b)) d a b)
termination_by lv _ _ _ => (lv, 0, 0, 0)
end

end Knot

end Lean.Kernel.InLean
