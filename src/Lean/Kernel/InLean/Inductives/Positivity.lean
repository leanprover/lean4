/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.Install

/-!
# InLean's inductive check: positivity

Twin of `ConLeche.Kernel.Inductives.Positivity` (nested positivity, its
container frames and seeds, the family telescopes) and of the positivity
entry of `ConLeche.Kernel.Inductives.BlockInstall` (`blockNestCtx`, `checkBlockPositivity`).
Placeholder variables (`nestPhs`, the canonical substitution's) are interned
before the pure walks that place them.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## Family telescopes -/

/-- Twin of `whnfTelescope`. -/
def whnfTelescope (ops : CheckerOps) (env : FEnv) : Nat → Nat → Expr → CheckCM (List Expr × Level)
  | i, 0, e => do
    match EO.stripTop (← ops.whnf env i e) with
    | .sort s => pure ([], s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    match EO.stripTop (← ops.whnf env i e) with
    | .forallE _ dom body _ =>
      let (bs, s) ← whnfTelescope ops env (i + 1) n (body.inst1I (← mkFVarM i dom))
      pure (dom :: bs, s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- Twin of `reducedFormer`.  The closing abstracts by depth
(`EO.abstractDepthsFrom`), which writes `EO.rangePoison` where a bound index
would pass C's bound: a reduct `EO.inRange` refuses is an error (as
`abstractRangeM` reports the marker). -/
def reducedFormer (ops : CheckerOps) (env : FEnv) (cv : ConstantVal) (n : Nat) :
    CheckCM ConstantVal := do
  let (bs, s) ← whnfTelescope ops env 0 n cv.type
  let ty := closeTelescope bs 0 (.sort s)
  if EO.inRange ty then pure { cv with type := ty }
  else throw (.internal "too many bound variables")

/-- Twin of `familyTelescope`. -/
def familyTelescope (ops : CheckerOps) (env : FEnv) (cv : ConstantVal) (caps : IndCaps) :
    CheckCM Expr :=
  if formerDefHeaded cv then do
    pure (← reducedFormer ops env cv (caps.nparams + caps.nIdx)).type
  else pure cv.type

/-- Twin of `checkSpineAt`. -/
def checkSpineAt (ops : CheckerOps) (env : FEnv) (d : Nat) : Expr → List Expr → CheckCM Unit
  | _, [] => pure ()
  | t, a :: as =>
    match EO.stripTop (t) with
    | .forallE _ ty body _ => do
      let ta ← ops.inferType env d a
      unless ← ops.isDefEq env d ta ty do
        throw (.invalid "application type mismatch at a family's parameters")
      checkSpineAt ops env d (body.inst1I a) as
    | _ => throw (.invalid "function expected at a family's parameters")

/-- Twin of `familyKeyCheck`. -/
def familyKeyCheck (ops : CheckerOps) (env : FEnv) (d : Nat) (c : Name) (us : List Level)
    (ds : List Expr) : CheckCM Unit :=
  match env.indView? c with
  | some (cv, caps) => do
    unless us.length = cv.levelParams.length do
      throw (.invalid "incorrect number of universe levels at a family's key")
    let ty ← familyTelescope ops env cv caps
    checkSpineAt ops env d (← instLevelParamsM cv.levelParams us ty) ds
  | none => throw (.invalid "a family's key is no stored family")

/-! ## The nested walk's records -/

/-- Twin of `NestKey`. -/
structure NestKey where
  cname : Name
  lvls : List Level
  ds : List Expr
  deriving BEq, Inhabited

/-- Twin of `NestHole`. -/
structure NestHole where
  key : NestKey
  base : Nat
  nIdx : Nat
  deriving BEq, Inhabited

/-- Twin of `fuelSlack`. -/
def fuelSlack : Nat := 1024

/-- Twin of `whnfWalkFuel`. -/
def whnfWalkFuel (e : Expr) : Nat := EO.depth e + fuelSlack

/-- Twin of `NestFieldKind`. -/
inductive NestFieldKind where
  | ordinary
  | recursive (tgt : Nat)
  | reflexive (tgt : Nat)
  | inProgress
  | nested (refl : Bool)
  deriving BEq, Inhabited

/-- Twin of `NestFieldKind.flat`. -/
def NestFieldKind.flat : NestFieldKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

/-- Twin of `nestKindsFlat`. -/
def nestKindsFlat (ks : List (List (List NestFieldKind))) : Bool :=
  ks.all (·.all (·.all NestFieldKind.flat))

/-- Twin of `NestCtorNf`. -/
structure NestCtorNf where
  ctor : Name
  lvls : List Level
  ds : List Expr
  ty : Expr
  deriving Inhabited

/-- Twin of `NestCtx` (the lookup is the environment's). -/
structure NestCtx where
  names : List Name
  lps : List Name
  nP : Nat
  nIdxs : List Nat
  params : List Expr
  sort : Level
  fe : FEnv
  formers : List ConstantVal

/-- Twin of `NestState`. -/
structure NestState where
  keys : Array NestKey := #[]
  active : List NestKey := []
  ctorNfs : Array NestCtorNf := #[]
  deriving Inhabited

/-- Twin of `nestCtorEntry`. -/
def nestCtorEntry (C : Name) (cv : ConstantVal) (nPc nF : Nat) : Option (ConstantVal × Nat × Nat) :=
  match stripPis (nPc + nF) cv.type with
  | some (_, body) =>
    match body.getAppFnT with
    | .const n _ => if n == C then some (cv, nPc, nF) else none
    | _ => none
  | none => none

/-- Twin of `nestContainer`. -/
def nestContainer (ctx : NestCtx) (C : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  match ctx.fe.indView? C with
  | some (_, caps) =>
    let cs := caps.ctors.filterMap fun n =>
      (ctx.fe.ctorView? n).bind fun (cv, nPc, nF) => nestCtorEntry C cv nPc nF
    match cs with
    | [] => some (caps.nparams, [])
    | (_, nPc, _) :: _ => some (nPc, cs.map fun c => (c.1, c.2.2))
  | none => none

/-- Twin of `nestNonValid`. -/
def nestNonValid : CheckError :=
  .invalid "nested positivity: non valid occurrence of the datatypes being declared"

/-- Twin of `NestCtx.hiAt`. -/
def NestCtx.hiAt (ctx : NestCtx) (nf : Nat) : Nat := ctx.nP + ctx.names.length + nf

/-- Twin of `NestCtx.rootHoles`. -/
def NestCtx.rootHoles (ctx : NestCtx) : List NestHole :=
  ctx.names.mapIdx fun t n => ⟨⟨n, ctx.lps.map .param, ctx.params⟩, ctx.nP, ctx.nIdxs.getD t 0⟩

/-- Twin of `nestHoleAt`. -/
def nestHoleAt (ctx : NestCtx) (prog : List NestHole) (i : Nat) : Option NestHole :=
  if ctx.nP ≤ i then (ctx.rootHoles ++ prog.reverse)[i - ctx.nP]? else none

/-- Twin of `nestHoleImg`. -/
def nestHoleImg (ctx : NestCtx) : List NestHole → Nat → Option Expr
  | [], i =>
    if ctx.nP ≤ i ∧ i < ctx.hiAt 0 then
      some (mkAppL (.const (ctx.names.getD (i - ctx.nP) .anonymous) (ctx.lps.map .param))
        ctx.params)
    else none
  | h :: prog, i =>
    if i = ctx.hiAt prog.length then
      some (mkAppL (.const h.key.cname h.key.lvls)
        (h.key.ds.map (replaceFVars (nestHoleImg ctx prog))))
    else nestHoleImg ctx prog i

/-- Twin of `Expr.phApp?`. -/
def phApp? (b : Nat) : Expr → Nat → Option (Name × List Level)
  | .const c us, 0 => some (c, us)
  | .mdata _ e, n => phApp? b e n
  | .app f x, n + 1 =>
    match EO.stripTop x with
    | .fvar id => if EO.fvDepth? id == some (b + n) then phApp? b f n else none
    | _ => none
  | _, _ => none

/-- Twin of `Expr.replaceApps`: an application of a constant to the variables
of depths `b … b + n - 1` replaced by `f`'s image. -/
def replaceApps (f : Name → List Level → Option Expr) (b n : Nat) (e : Expr) : Expr :=
  EO.replace (fun x =>
    match EO.stripTop (x) with
    | .app .. | .const .. => (phApp? b x n).bind fun p => f p.1 p.2
    | _ => none) e

/-- Twin of `nestPhs`: the placeholders of depths `0 … n - 1`, each of type
`Sort 0`. -/
def nestPhs (n : Nat) : CheckCM (List Expr) :=
  (List.range n).mapM fun i => mkFVarM i (.sort .zero)

/-- The placeholders of the members, at depths `n + m` (`nestCanonSub`'s images). -/
def nestCanonVars (names : List Name) (n : Nat) : CheckCM (List Expr) :=
  (List.range names.length).mapM fun m => mkFVarM (n + m) (.sort .zero)

/-- Twin of `nestCanonSub` (its placeholders interned beforehand, `vars`). -/
def nestCanonSub (names : List Name) (us : List Level) (vars : List Expr) :
    Name → List Level → Option Expr :=
  fun c v => if v == us then (names.findIdx? (· == c)).bind (vars[·]?) else none

/-- Twin of `nestCanonCrest`. -/
def nestCanonCrest (names : List Name) (us : List Level) (n : Nat) (cty : Expr) :
    CheckCM (Option Expr) := do
  let phs ← nestPhs n
  let vars ← nestCanonVars names n
  return (instPisWith phs cty).map (replaceApps (nestCanonSub names us vars) 0 n)

/-- Twin of `nestKeyMap`. -/
def nestKeyMap (ds holes : List Expr) : Nat → Option Expr :=
  fun i => if i < ds.length then ds[i]? else holes[i - ds.length]?

/-- Twin of `nestCrest`. -/
def nestCrest (names : List Name) (us : List Level) (ds holes : List Expr) (cty : Expr) :
    CheckCM (Option Expr) := do
  return (← nestCanonCrest names us ds.length cty).map (replaceFVars (nestKeyMap ds holes))

/-- Twin of `nestInstType`. -/
def nestInstType (ctx : NestCtx) (ops : CheckerOps) (env : FEnv) (hi : Nat) (key : NestKey) :
    CheckCM (Nat × Expr) := do
  let (cvC, capsC) ← unwrapOr (ctx.fe.indView? key.cname)
    (.internal "nested positivity: container vanished")
  unless key.lvls.length = cvC.levelParams.length do
    throw (.invalid "nested positivity: incorrect number of universe levels for a nested \
      inductive datatype (official: incorrect number of universe levels)")
  let tyC ← familyTelescope ops env cvC capsC
  unless (stripPis key.ds.length tyC).isSome do
    throw (.invalid "nested positivity: invalid nested inductive datatype, its type does \
      not bind its parameters (official: ill-formed inductive type)")
  let ty ← unwrapOr (instPisWith key.ds (← instLevelParamsM cvC.levelParams key.lvls tyC))
    (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind \
      its parameters (official: ill-formed inductive type)")
  let s ← unwrapOr (match (piBinders ty).2 with
      | .sort s => some s
      | _ => none)
    (.invalid "nested positivity: invalid nested inductive datatype, its type is not a \
      telescope ending in a sort (official: type expected)")
  if (piBinders ty).1.any (fun b => nestOcc ctx.names ctx.nP hi b) then
    throw (.invalid "nested positivity: a container's index telescope mentions the block \
      (official: unknown constant)")
  unless ← liftFueled "level comparison" (Lvl.isEquiv s ctx.sort) do
    throw (.invalid "nested positivity: mutually inductive types must live in the \
      same universe")
  pure ((piBinders ty).1.length, ty)

/-- Twin of `nestResHead`. -/
def nestResHead (e : Expr) : Bool := e.getAppFnT.isFVar

/-- The recursion a container's constructors are walked with. -/
abbrev NestRec := List NestHole → Nat → Nat → Expr → NestState →
  CheckCM (NestFieldKind × Expr × NestState)

/-- Twin of `nestFields`. -/
def nestFields (rec : NestRec) (prog : List NestHole) (base : Nat) (err : CheckError) :
    Nat → Nat → Expr → NestState → CheckCM (List NestFieldKind × List Expr × Expr × NestState)
  | 0, _, cur, st => pure ([], [], cur, st)
  | nF + 1, j, cur, st =>
    match EO.stripTop (cur) with
    | .forallE _ a b _ => do
      let (k, nd, st) ← rec prog (base + j) 0 a st
      let (ks, nds, res, st) ← nestFields rec prog base err nF (j + 1)
        (b.inst1I (← mkFVarM (base + j) a)) st
      pure (k :: ks, nd :: nds, res, st)
    | _ => throw err

/-- Twin of `nestCtorNf`. -/
def nestCtorNf (ctx : NestCtx) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (cv : ConstantVal) (nds : List Expr) (cur : Expr) : NestCtorNf :=
  ⟨cv.name, us, ds.map (replaceFVars (nestHoleImg ctx prog)),
    replaceFVars (nestHoleImg ctx prog) (closeTelescope nds hi cur)⟩

/-- Twin of `nestCtors`. -/
def nestCtors (ctx : NestCtx) (ops : CheckerOps) (env : FEnv) (rec : Expr → NestRec)
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name)
    (holes : List Expr) :
    List (ConstantVal × Nat) → NestState → CheckCM (List (List NestFieldKind × Expr) × NestState)
  | [], st => pure ([], st)
  | (cv, nF) :: cs, st => do
    unless namesNodup cv.levelParams do
      throw (.invalid "nested positivity: invalid nested inductive datatype, its constructor \
        has a duplicate universe level parameter (official: duplicate universe level \
        parameter)")
    let crest ← unwrapOr
      (← nestCrest names us ds holes (← instLevelParamsM cv.levelParams us cv.type))
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind the parameters (official: ill-formed constructor)")
    let ty ← ops.inferType env hi crest
    let _ ← ops.ensureSort env hi ty
    let (ks, nds, cur, st) ← nestFields (rec crest) prog hi
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind its fields (official: ill-formed constructor)") nF 0 crest st
    if (closeTelescope nds hi cur).hasExprMVar then
      throw (.internal "too many bound variables")
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds hi cur) 0 i) then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a later field or the result depends on a recursive or nested field)")
    unless nestResHead cur && (appArgs cur).all (fun x => !nestOcc ctx.names ctx.nP hi x) do
      throw (.invalid "nested positivity: invalid return type — a constructor's result \
        index mentions the block")
    let st := { st with ctorNfs := st.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur) }
    let (os, st) ← nestCtors ctx ops env rec prog hi us ds names holes cs st
    pure ((ks, closeTelescope nds hi cur) :: os, st)

/-- Twin of `nestGroupCtors`. -/
def nestGroupCtors (ctx : NestCtx) (nPc : Nat) : List Name → CheckCM (List (ConstantVal × Nat))
  | [] => pure []
  | c :: cs => do
    let (nPc', ctors) ← unwrapOr (nestContainer ctx c) nestNonValid
    unless nPc' == nPc || ctors.isEmpty do
      throw (.invalid "nested positivity: number of parameters mismatch in inductive \
        datatype declaration (a container's group)")
    let rest ← nestGroupCtors ctx nPc cs
    pure (ctors ++ rest)

/-- Twin of `nestBlockOf`. -/
def nestBlockOf (ctx : NestCtx) (C : Name) : List Name :=
  match ctx.fe.indView? C with
  | some (_, caps) => caps.all
  | none => []

/-- Twin of `nestFrameMates`. -/
def nestFrameMates (ctx : NestCtx) (C : Name) : List Name :=
  (nestBlockOf ctx C).eraseDups.filter (· != C)

/-- Twin of `nestGrowGroup`. -/
def nestGrowGroup (ctx : NestCtx) (ops : CheckerOps) (env : FEnv) (hi : Nat) (us : List Level)
    (ds : List Expr) : List Name → List (Name × Expr) → CheckCM (List (Name × Expr))
  | [], grp => pure grp
  | c :: cs, grp => do
    let (_, cty) ← nestInstType ctx ops env hi ⟨c, us, ds⟩
    nestGrowGroup ctx ops env hi us ds cs (grp ++ [(c, cty)])

/-- Twin of `nestAcceptGroup`. -/
def nestAcceptGroup (us : List Level) (ds : List Expr) :
    List (Name × Expr) → Array NestKey → Array NestKey
  | [], keys => keys
  | (c, _) :: rest, keys =>
    nestAcceptGroup us ds rest (if keys.contains ⟨c, us, ds⟩ then keys else keys.push ⟨c, us, ds⟩)

/-- Twin of `nestFrame`. -/
def nestFrame (ctx : NestCtx) (ops : CheckerOps) (env : FEnv) (rec : NestRec)
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) : CheckCM NestState := do
  familyKeyCheck ops env hi (grp.headD default).1 us ds
  let prog' := (grp.mapIdx fun _ (c, ty) =>
    ({ key := ⟨c, us, ds⟩, base := hi, nIdx := (piBinders ty).1.length } : NestHole)).reverse ++ prog
  let ctors ← nestGroupCtors ctx nPc (grp.map (·.1))
  let holes ← (List.range grp.length).mapM fun i => mkFVarM (hi + i) (grp.getD i default).2
  let (_, st) ← nestCtors ctx ops env (fun _ => rec) prog' (hi + grp.length) us ds (grp.map (·.1))
    holes ctors st
  pure st

/-- Twin of `nestWalkStack`. -/
def nestWalkStack (ctx : NestCtx) (prog : List NestHole) (ds : List Expr) : List NestHole :=
  if ds.all (fun x => fvarB x ≤ ctx.hiAt 0) then [] else prog

/-- Twin of `nestContNew`. -/
def nestContNew (ctx : NestCtx) (ops : CheckerOps) (env : FEnv) (rec : NestRec)
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : CheckCM (NestFieldKind × NestState) := do
  let wp := nestWalkStack ctx prog ds
  let grp ← nestGrowGroup ctx ops env (ctx.hiAt wp.length) us ds (nestFrameMates ctx n) [(n, cty)]
  let act := st.active
  let st := { st with active := grp.map (fun p => ({ cname := p.1, lvls := us, ds := ds } : NestKey))
                                  ++ act }
  let st ← nestFrame ctx ops env rec wp (ctx.hiAt wp.length) us ds nPc grp st
  return (.nested (kb != 0),
    { st with active := act,
              keys := if ds.all (fun x => fvarB x ≤ ctx.hiAt 0) then
                nestAcceptGroup us ds grp st.keys else st.keys })

/-- Twin of `nestContKey`. -/
def nestContKey (ctx : NestCtx) (ops : CheckerOps) (env : FEnv) (rec : NestRec)
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : CheckCM (NestFieldKind × NestState) :=
  if st.active.contains ⟨n, us, ds⟩ then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (an instantiation in progress, reached through reduction)")
  else if ds.all (fun x => fvarB x ≤ ctx.hiAt 0) && st.keys.contains ⟨n, us, ds⟩ then
    pure (.nested (kb != 0), st)
  else nestContNew ctx ops env rec prog kb n us ds nPc cty st

/-- Twin of `nestCont`. -/
def nestCont (ctx : NestCtx) (ops : CheckerOps) (env : FEnv) (rec : NestRec)
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) : CheckCM (NestFieldKind × NestState) := do
  let q ← unwrapOr (nestContainer ctx n) nestNonValid
  if args.length < q.1 ||
      !(args.drop q.1).all (fun x => !nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) then
    throw nestNonValid
  if n == quotName then throw nestNonValid
  unless (args.take q.1).all (fun x => !x.hasLooseBVars && fvarB x ≤ ctx.hiAt prog.length) do
    throw (.invalid "nested positivity: nested inductive datatypes parameters \
      cannot contain local variables")
  let ni ← nestInstType ctx ops env (ctx.hiAt prog.length) ⟨n, us, args.take q.1⟩
  unless args.length == q.1 + ni.1 do
    throw (.invalid "nested positivity: type expected (a container instance that is not \
      fully applied)")
  nestContKey ctx ops env rec prog kb n us (args.take q.1) q.1 ni.2 st

/-- Twin of `nestPos`. -/
def nestPos (ops : CheckerOps) (env : FEnv) (ctx : NestCtx) : Nat → NestRec
  | 0, _, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, prog, dep, kb, e, st => do
    let hi := ctx.hiAt prog.length
    let w ← ops.whnf env dep e
    if !nestOcc ctx.names ctx.nP hi w then
      return (.ordinary, (if nestOcc ctx.names ctx.nP hi e then w else e), st)
    match EO.stripTop (w) with
    | .forallE _ a b _ =>
      if nestOcc ctx.names ctx.nP hi a then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      let (k, nb, st) ←
        nestPos ops env ctx fuel prog (dep + 1) (kb + 1) (b.inst1I (← mkFVarM dep a)) st
      let nb := abstract1 nb dep 0
      if nb.hasExprMVar then throw (.internal "too many bound variables")
      pure (k, .forallE .anonymous a nb .default, st)
    | _ =>
      let args := appArgs w
      match w.getAppFnT with
      | .fvar id =>
        let i := (EO.fvDepth? id).getD 0
        match nestHoleAt ctx prog i with
        | some h =>
          if args.all (fun x => !nestOcc ctx.names ctx.nP hi x) && args.length == h.nIdx then
            return (if i < ctx.hiAt 0 then
                (if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP))
              else .inProgress, w, st)
          else throw nestNonValid
        | none => throw nestNonValid
      | .const n us =>
        if ctx.names.contains n then throw nestNonValid
        let (k, st) ← nestCont ctx ops env (nestPos ops env ctx fuel) prog kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

/-- Twin of `nestHoles`. -/
def nestHoles (ctx : NestCtx) : CheckCM (Option (List Expr)) := do
  let mut out : Array Expr := #[]
  for mm in List.range ctx.names.length do
    match ctx.formers[mm]? with
    | some cv =>
      match instPisWith ctx.params cv.type with
      | some ty => out := out.push (← mkFVarM (ctx.nP + mm) ty)
      | none => return none
    | none => return none
  return some out.toList

/-- Twin of `nestRootCanon`. -/
def nestRootCanon (ctx : NestCtx) (cv : ConstantVal) : CheckCM (Option Expr) :=
  nestCanonCrest ctx.names (ctx.lps.map .param) ctx.nP
    (cv.type.instLvlParamsI cv.levelParams (ctx.lps.map .param))

/-- Twin of `Expr.piDomsOcc`. -/
def piDomsOcc (names : List Name) (lo hi : Nat) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, .forallE _ d b _ => nestOcc names lo hi d || piDomsOcc names lo hi n b
  | n + 1, .mdata _ e => piDomsOcc names lo hi (n + 1) e
  | _ + 1, _ => false

/-- Twin of `nestUniformOk`. -/
def nestUniformOk (ctx : NestCtx) (cv : ConstantVal) : CheckCM Bool := do
  if piDomsOcc ctx.names ctx.nP (ctx.hiAt 0) ctx.nP cv.type then return false
  match ← nestRootCanon ctx cv with
  | some crest => return !nestOcc ctx.names 0 0 crest
  | none => return false

/-- Twin of `nestUniform`. -/
def nestUniform (ctx : NestCtx) (ctorss : List (List (ConstantVal × Nat))) : CheckCM Unit := do
  for cs in ctorss do
    for c in cs do
      unless ← nestUniformOk ctx c.1 do
        throw (.invalid s!"invalid occurrence of a datatype being declared in the \
          type of {c.1.name}: it must be applied to the parameters and universe levels of the \
          mutual declaration")

/-- Twin of `nestRoot`. -/
def nestRoot (ops : CheckerOps) (env : FEnv) (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → NestState →
      CheckCM (List (List (List NestFieldKind × Expr)) × NestState)
  | [], st => pure ([], st)
  | cs :: css, st => do
    let (o, st) ← nestCtors ctx ops env (fun crest => nestPos ops env ctx (whnfWalkFuel crest)) []
      (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.names holes cs st
    let (os, st) ← nestRoot ops env ctx holes css st
    pure (o :: os, st)

/-- Twin of `nestSeedOf`. -/
def nestSeedOf (ctx : NestCtx) (holes : List Expr) (I : Name) (us : List Level) (ds : List Expr)
    (nPc : Nat) : CheckCM (NestKey × Nat) := do
  let vars ← nestCanonVars ctx.names ctx.nP
  return (⟨I, us, ds.map fun x =>
      replaceFVars (nestKeyMap ctx.params holes)
        (replaceApps (nestCanonSub ctx.names (ctx.lps.map .param) vars) 0 ctx.nP x)⟩, nPc)

/-- Twin of `nestSeeds`. -/
def nestSeeds (ops : CheckerOps) (env : FEnv) (ctx : NestCtx) :
    List (NestKey × Nat) → NestState → CheckCM NestState
  | [], st => pure st
  | (key, nPc) :: ks, st => do
    let F := key.ds.foldl (fun a d => max a (whnfWalkFuel d)) fuelSlack
    let (_, cty) ← nestInstType ctx ops env (ctx.hiAt 0) key
    let (_, st) ← nestContKey ctx ops env (nestPos ops env ctx F) [] 0 key.cname key.lvls key.ds
      nPc cty st
    nestSeeds ops env ctx ks st

/-! ## The block's positivity (twins of `ConLeche.Kernel.Inductives.BlockInstall`'s) -/

/-- Twin of `BlockShape.nestCtx`. -/
def BlockShape.nestCtx (p : BlockShape) (fvsP : List Expr) (fe : FEnv) : NestCtx :=
  ⟨p.memberNames, p.lps, p.nP, p.nIdxs, fvsP, p.resSort, fe, p.members.map (·.cvT)⟩

/-- Twin of `checkAbsCtorSorts`. -/
def checkAbsCtorSorts (ops : CheckerOps) (env : FEnv) (ctx : NestCtx) :
    List (ConstantVal × Nat) → List (List NestFieldKind × Expr) → CheckCM Unit
  | c :: cs, o :: os => do
    unless ← allLevelParamsDefined ctx.lps o.2 do
      throw (.internal "direct rec: a positivity normal form outside the block's level \
        parameters")
    let xq ← unwrapOr (← openPisAtFvars c.2 o.2 (ctx.hiAt 0))
      (.internal "direct rec: abstracted constructor fields")
    checkStructFieldSortsIF ops env (Lvl.isEquiv ctx.sort .zero == some true) false ctx.sort
      (ctx.hiAt 0) xq.1 [] c.2
    checkAbsCtorSorts ops env ctx cs os
  | _, _ => pure ()

/-- Twin of `checkAbsCtorSortsAll`. -/
def checkAbsCtorSortsAll (ops : CheckerOps) (env : FEnv) (ctx : NestCtx) :
    List (List (ConstantVal × Nat)) → List (List (List NestFieldKind × Expr)) → CheckCM Unit
  | cs :: css, os :: oss => do
    checkAbsCtorSorts ops env ctx cs os
    checkAbsCtorSortsAll ops env ctx css oss
  | _, _ => pure ()

/-- Twin of `blockNestCtx`. -/
def blockNestCtx (p : BlockShape) (fe : FEnv) : CheckCM (NestCtx × List Expr) := do
  let cvTa0 ← unwrapOr p.formers.head? (.internal "direct rec: no type former")
  let pq ← unwrapOr (← openPisAtFvars p.nP cvTa0.type 0)
    (.internal "direct rec: type former telescope")
  let ctx := p.nestCtx pq.1 fe
  let holes ← unwrapOr (← nestHoles ctx) (.internal "direct rec: a member is not a stored former")
  pure (ctx, holes)

/-- Twin of `nestOutKinds`. -/
def nestOutKinds (outs : List (List (List NestFieldKind × Expr))) : List (List (List NestFieldKind)) :=
  outs.map (·.map (·.1))

/-- Twin of `checkBlockPositivity`. -/
def checkBlockPositivity (ops : CheckerOps) (env₁ : FEnv) (p : BlockShape) :
    CheckCM (List (List (List NestFieldKind × Expr)) × NestState) := do
  let (ctx, holes) ← blockNestCtx p env₁
  nestUniform ctx p.memberCtors
  let (outs, st) ← nestRoot ops env₁ ctx holes p.memberCtors {}
  checkAbsCtorSortsAll ops env₁ ctx p.memberCtors outs
  pure (outs, st)

end Lean.Kernel.InLean
