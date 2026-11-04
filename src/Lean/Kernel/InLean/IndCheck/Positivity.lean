/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.IndCheck.Install

/-!
# InLean's inductive checker: nested positivity

Twin of `Kernel/Inductives/Positivity.lean`:
con-leche's positivity walk over a block's constructors, nested
occurrences included, by container frames (no auxiliary declaration):
the members are *holes* (variables of levels `nP … nP+k-1`), a nested
container's instantiation opens a frame whose members are holes at the
next levels, and every constructor's field is classified
(`NestFieldKind`) and normalised; the walk records each container
instantiation it accepted (`NestState.keys`) and every constructor's
normal form (`ctorNfs`), which the recursor stage reads.

The functions are con-leche's, clause by clause; the level-indexed
variable operations go through `Lean/Kernel/InLean/IndCheck/Base.lean`.  The pure
image maps con-leche writes as recursive functions of a level
(`nestHoleImg`, `nestCanonSub`) are tabulated up front, since building a
variable is a state operation here.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

namespace IC

structure NestKey where
  cname : Name
  lvls : List Level
  ds : List Expr
  deriving Inhabited

instance : BEq NestKey := ⟨fun a b => a.cname == b.cname && a.lvls == b.lvls && listAlpha a.ds b.ds⟩

structure NestHole where
  key : NestKey
  base : Nat
  deriving Inhabited

inductive NestFieldKind where
  | ordinary
  | recursive (tgt : Nat)
  | reflexive (tgt : Nat)
  | inProgress
  | nested (refl : Bool)
  deriving Inhabited, BEq

def NestFieldKind.flat : NestFieldKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

def nestKindsFlat (ks : List (List (List NestFieldKind))) : Bool :=
  ks.all (·.all (·.all NestFieldKind.flat))

structure NestCtorNf where
  ctor : Name
  lvls : List Level
  ds : List Expr
  ty : Expr
  deriving Inhabited

structure NestCtx where
  names : List Name
  lps : List Name
  nP : Nat
  nIdxs : List Nat
  params : List Expr
  sort : Level
  env : Kernel.Environment

structure NestState where
  keys : Array NestKey := #[]
  active : List NestKey := []
  ctorNfs : Array NestCtorNf := #[]
  deriving Inhabited

def fuelSlack : Nat := 1024

/-- Twin of `whnfWalkFuel` (the term's depth plus slack). -/
def exprDepth (e : Expr) : Nat := EO.depth e

def whnfWalkFuel (e : Expr) : Nat := exprDepth e + fuelSlack

/-- Twin of `nestCtorEntry`. -/
def nestCtorEntry (C : Name) (cv : CV) (nPc nF : Nat) : Option (CV × Nat × Nat) :=
  match stripPis (nPc + nF) cv.type with
  | some (_, body) =>
    match body.getAppFn with
    | .const n _ => if n == C then some (cv, nPc, nF) else none
    | _ => none
  | none => none

/-- Twin of `nestContainer`. -/
def nestContainer (env : Kernel.Environment) (C : Name) : Option (Nat × List (CV × Nat)) :=
  match indView? env C with
  | some iv =>
    let cs := iv.ctors.filterMap fun n =>
      (ctorView? env n).bind fun (cv, nPc, nF) => nestCtorEntry C cv nPc nF
    match cs with
    | [] => some (iv.nparams, [])
    | (_, nPc, _) :: _ => some (nPc, cs.map fun c => (c.1, c.2.2))
  | none => none

def nestNonValid : Err := .invalid "nested positivity: non valid occurrence of the datatypes being declared"

def NestCtx.hiAt (ctx : NestCtx) (nf : Nat) : Nat := ctx.nP + ctx.names.length + nf

def NestCtx.rootHoles (ctx : NestCtx) : List NestHole :=
  ctx.names.map fun n => ⟨⟨n, ctx.lps.map .param, ctx.params⟩, ctx.nP⟩

def nestHoleAt (ctx : NestCtx) (prog : List NestHole) (i : Nat) : Option NestHole :=
  if ctx.nP ≤ i then (ctx.rootHoles ++ prog.reverse)[i - ctx.nP]? else none

/-- Twin of `nestHoleImg`, tabulated: the image of every hole level below
`hiAt prog.length`. -/
def nestHoleImgs (ctx : NestCtx) : List NestHole → M (Array (Option Expr))
  | [] => do
    let mut a : Array (Option Expr) := Array.replicate (ctx.hiAt 0) none
    for i in [ctx.nP:ctx.hiAt 0] do
      a := a.set! i (some (mkAppL (.const (ctx.names.getD (i - ctx.nP) .anonymous)
        (ctx.lps.map .param)) ctx.params))
    return a
  | h :: prog => do
    let a ← nestHoleImgs ctx prog
    let ds ← h.key.ds.mapM (replaceFVars fun i => (a[i]?).join)
    return a.push (some (mkAppL (.const h.key.cname h.key.lvls) ds))

def holeImgFn (a : Array (Option Expr)) : Nat → Option Expr := fun i => (a[i]?).join

/-- Twin of `Expr.phApp?`. -/
def phApp? (deps : Array Nat) (b : Nat) : Expr → Nat → Option (Name × List Level)
  | .const c us, 0 => some (c, us)
  | .app f (.fvar j), n + 1 => if lvlOf deps j == some (b + n) then phApp? deps b f n else none
  | _, _ => none

/-- Twin of `Expr.replaceApps` (memoised by `Expr.replace`). -/
def replaceApps (f : Name → List Level → Option Expr) (b n : Nat) (e : Expr) : M Expr := do
  let deps ← depths
  return e.replaceI fun t =>
    match t with
    | .app .. | .const .. => (phApp? deps b t n).bind fun p => f p.1 p.2
    | _ => none

/-- Twin of `nestPhs`. -/
def nestPhs (n : Nat) : M (List Expr) := (List.range n).mapM fun i => fvar i (.sort .zero)

/-- Twin of `nestCanonSub`, its placeholders prebuilt. -/
def nestCanonSub (names : List Name) (us : List Level) (n : Nat) :
    M (Name → List Level → Option Expr) := do
  let phs ← (List.range names.length).mapM fun m => fvar (n + m) (.sort .zero)
  return fun c v => if v == us then (names.findIdx? (· == c)).bind (phs[·]?) else none

/-- Twin of `nestCanonCrest`. -/
def nestCanonCrest (names : List Name) (us : List Level) (n : Nat) (cty : Expr) : M (Option Expr) := do
  match instPisWith (← nestPhs n) cty with
  | some e => return some (← replaceApps (← nestCanonSub names us n) 0 n e)
  | none => return none

def nestKeyMap (ds holes : List Expr) : Nat → Option Expr :=
  fun i => if i < ds.length then ds[i]? else holes[i - ds.length]?

/-- Twin of `nestCrest`. -/
def nestCrest (names : List Name) (us : List Level) (ds holes : List Expr) (cty : Expr) :
    M (Option Expr) := do
  match ← nestCanonCrest names us ds.length cty with
  | some c => return some (← replaceFVars (nestKeyMap ds holes) c)
  | none => return none

/-- Twin of `nestInstType`. -/
def nestInstType (ctx : NestCtx) (hi : Nat) (key : NestKey) : M (Nat × Expr) := do
  let iv ← unwrapOr (indView? ctx.env key.cname) (.internal "nested positivity: container vanished")
  let cvC := iv.cv
  unless key.lvls.length == cvC.lps.length do
    throwInvalid "nested positivity: incorrect number of universe levels for a nested inductive \
      datatype (official: incorrect number of universe levels)"
  unless (stripPis key.ds.length cvC.type).isSome do
    throwInvalid "nested positivity: invalid nested inductive datatype, its type does not bind \
      its parameters (official: ill-formed inductive type)"
  let ty ← unwrapOr (instPisWith key.ds (cvC.type.instLvlParamsI cvC.lps key.lvls))
    (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its \
      parameters (official: ill-formed inductive type)")
  let s ← unwrapOr (match (piBinders ty).2 with | .sort s => some s | _ => none)
    (.invalid "nested positivity: invalid nested inductive datatype, its type is not a telescope \
      ending in a sort (official: type expected)")
  let deps ← depths
  if (piBinders ty).1.any (fun b => nestOcc deps ctx.names ctx.nP hi b) then
    throwInvalid "nested positivity: a container's index telescope mentions the block \
      (official: unknown constant)"
  unless ← isEquivL s ctx.sort do
    throwInvalid "nested positivity: mutually inductive types must live in the same universe"
  pure ((piBinders ty).1.length, ty)

def nestResHead (e : Expr) : Bool := e.getAppFn.isFVar

/-- Twin of `nestCtorNf`. -/
def nestCtorNf (ctx : NestCtx) (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
    (cv : CV) (nds : List Expr) (cur : Expr) : M NestCtorNf := do
  let imgs ← nestHoleImgs ctx prog
  let f := holeImgFn imgs
  return ⟨cv.name, us, ← ds.mapM (replaceFVars f), ← replaceFVars f (← closeTelescope nds hi cur)⟩

/-- Twin of `structUsedLater`. -/
def structUsedLater (cty : Expr) (nP k : Nat) : Bool :=
  match stripPis (nP + k + 1) cty with
  | some (_, rest) => rest.hasLooseBVarI 0
  | none => false

/-- Twin of `nestGroupCtors`. -/
def nestGroupCtors (ctx : NestCtx) (nPc : Nat) : List Name → M (List (CV × Nat))
  | [] => pure []
  | c :: cs => do
    let (nPc', ctors) ← unwrapOr (nestContainer ctx.env c) nestNonValid
    unless nPc' == nPc || ctors.isEmpty do
      throwInvalid "nested positivity: number of parameters mismatch in inductive datatype \
        declaration (a container's group)"
    pure (ctors ++ (← nestGroupCtors ctx nPc cs))

def nestBlockOf (ctx : NestCtx) (C : Name) : List Name :=
  (indView? ctx.env C).map (·.all) |>.getD []

def nestFrameMates (ctx : NestCtx) (C : Name) : List Name :=
  (nestBlockOf ctx C).eraseDups.filter (· != C)

def nestArity (ctx : NestCtx) (C : Name) : Nat :=
  match indView? ctx.env C with
  | some iv => (piBinders iv.cv.type).1.length
  | none => 0

def nestGrowGroup (ctx : NestCtx) (hi : Nat) (us : List Level) (ds : List Expr) :
    List Name → List (Name × Expr) → M (List (Name × Expr))
  | [], grp => pure grp
  | c :: cs, grp => do
    let (_, cty) ← nestInstType ctx hi ⟨c, us, ds⟩
    nestGrowGroup ctx hi us ds cs (grp ++ [(c, cty)])

def nestAcceptGroup (us : List Level) (ds : List Expr) : List (Name × Expr) → Array NestKey → Array NestKey
  | [], keys => keys
  | (c, _) :: rest, keys =>
    nestAcceptGroup us ds rest (if keys.contains ⟨c, us, ds⟩ then keys else keys.push ⟨c, us, ds⟩)

/-- The recursion every constructor walk takes (`nestPos` at its fuel). -/
abbrev NestRec := List NestHole → Nat → Nat → Expr → NestState → M (NestFieldKind × Expr × NestState)

/-- Twin of `nestFields`. -/
def nestFields (rec : NestRec) (prog : List NestHole) (base : Nat) (err : Err) :
    Nat → Nat → Expr → NestState → M (List NestFieldKind × List Expr × Expr × NestState)
  | 0, _, cur, st => pure ([], [], cur, st)
  | nF + 1, k, cur, st =>
    match cur with
    | .forallE _ a b _ => do
      let (kd, nd, st) ← rec prog (base + k) 0 a st
      let (ks, nds, res, st) ← nestFields rec prog base err nF (k + 1)
        (b.inst1I (← fvar (base + k) a)) st
      pure (kd :: ks, nd :: nds, res, st)
    | _ => throw err

/-- Twin of `nestCtors`. -/
def nestCtors (ctx : NestCtx) (j : Job) (env : Kernel.Environment) (rec : Expr → NestRec)
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name)
    (holes : List Expr) : List (CV × Nat) → NestState → M (List (List NestFieldKind × Expr) × NestState)
  | [], st => pure ([], st)
  | (cv, nF) :: cs, st => do
    unless nodup cv.lps do
      throwInvalid "nested positivity: invalid nested inductive datatype, its constructor has a \
        duplicate universe level parameter (official: duplicate universe level parameter)"
    let crest ← unwrapOr (← nestCrest names us ds holes (cv.type.instLvlParamsI cv.lps us))
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type does \
        not bind the parameters (official: ill-formed constructor)")
    let ty ← j.infer env hi crest
    let _ ← j.ensureSort env hi ty
    let (ks, nds, cur, st) ← nestFields (rec crest) prog hi
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type does \
        not bind its fields (official: ill-formed constructor)") nF 0 crest st
    let closed ← closeTelescope nds hi cur
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary && structUsedLater closed 0 i) then
      throwInvalid "nested positivity: non valid occurrence of the datatypes being declared (a later \
        field or the result depends on a recursive or nested field)"
    let deps ← depths
    unless nestResHead cur && cur.getAppArgs.all (fun x => !nestOcc deps ctx.names ctx.nP hi x) do
      throwInvalid "nested positivity: invalid return type — a constructor's result index mentions \
        the block"
    let nf ← nestCtorNf ctx prog hi us ds cv nds cur
    let st := { st with ctorNfs := st.ctorNfs.push nf }
    let (os, st) ← nestCtors ctx j env rec prog hi us ds names holes cs st
    pure ((ks, closed) :: os, st)

/-- Twin of `nestWalkStack`. -/
def nestWalkStack (ctx : NestCtx) (prog : List NestHole) (ds : List Expr) : M (List NestHole) := do
  for x in ds do
    if (← fvarB x) > ctx.hiAt 0 then return prog
  return []

def dsClosedAtRoot (ctx : NestCtx) (ds : List Expr) : M Bool := do
  for x in ds do
    if (← fvarB x) > ctx.hiAt 0 then return false
  return true

/-- Twin of `nestFrame`. -/
def nestFrame (ctx : NestCtx) (j : Job) (env : Kernel.Environment) (rec : NestRec)
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) : M NestState := do
  let _ ← j.infer env hi (mkAppL (.const (grp.headD default).1 us) ds)
  let prog' := (grp.map fun (c, _) => ({ key := ⟨c, us, ds⟩, base := hi } : NestHole)).reverse ++ prog
  let ctors ← nestGroupCtors ctx nPc (grp.map (·.1))
  let holes ← (List.range grp.length).mapM fun i => fvar (hi + i) (grp.getD i default).2
  let (_, st) ← nestCtors ctx j env (fun _ => rec) prog' (hi + grp.length) us ds (grp.map (·.1))
    holes ctors st
  pure st

/-- Twin of `nestContNew`. -/
def nestContNew (ctx : NestCtx) (j : Job) (env : Kernel.Environment) (rec : NestRec)
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : M (NestFieldKind × NestState) := do
  let wp ← nestWalkStack ctx prog ds
  let grp ← nestGrowGroup ctx (ctx.hiAt wp.length) us ds (nestFrameMates ctx n) [(n, cty)]
  let act := st.active
  let st := { st with active := grp.map (fun p => ({ cname := p.1, lvls := us, ds := ds } : NestKey)) ++ act }
  let st ← nestFrame ctx j env rec wp (ctx.hiAt wp.length) us ds nPc grp st
  let closed ← dsClosedAtRoot ctx ds
  return (.nested (kb != 0),
    { st with active := act, keys := if closed then nestAcceptGroup us ds grp st.keys else st.keys })

/-- Twin of `nestContKey`. -/
def nestContKey (ctx : NestCtx) (j : Job) (env : Kernel.Environment) (rec : NestRec)
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : M (NestFieldKind × NestState) := do
  if st.active.contains ⟨n, us, ds⟩ then
    throwInvalid "nested positivity: non valid occurrence of the datatypes being declared (an \
      instantiation in progress, reached through reduction)"
  else if (← dsClosedAtRoot ctx ds) && st.keys.contains ⟨n, us, ds⟩ then
    pure (.nested (kb != 0), st)
  else nestContNew ctx j env rec prog kb n us ds nPc cty st

/-- Twin of `nestCont`. -/
def nestCont (ctx : NestCtx) (j : Job) (env : Kernel.Environment) (rec : NestRec)
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) : M (NestFieldKind × NestState) := do
  let q ← unwrapOr (nestContainer ctx.env n) nestNonValid
  let deps ← depths
  if args.length < q.1 ||
      !(args.drop q.1).all (fun x => !nestOcc deps ctx.names ctx.nP (ctx.hiAt prog.length) x) then
    throw nestNonValid
  if n == quotName then throw nestNonValid
  for x in args.take q.1 do
    unless bvarB x == 0 && (← fvarB x) ≤ ctx.hiAt prog.length do
      throwInvalid "nested positivity: nested inductive datatypes parameters cannot contain local \
        variables"
  let ni ← nestInstType ctx (ctx.hiAt prog.length) ⟨n, us, args.take q.1⟩
  unless args.length == q.1 + ni.1 do
    throwInvalid "nested positivity: type expected (a container instance that is not fully applied)"
  nestContKey ctx j env rec prog kb n us (args.take q.1) q.1 ni.2 st

/-- Twin of `nestPos`. -/
def nestPos (j : Job) (env : Kernel.Environment) (ctx : NestCtx) :
    Nat → List NestHole → Nat → Nat → Expr → NestState → M (NestFieldKind × Expr × NestState)
  | 0, _, _, _, _, _ => throwDeclined "nested positivity: fuel"
  | fuel + 1, prog, dep, kb, e, st => do
    let hi := ctx.hiAt prog.length
    let w ← j.whnf env dep e
    let deps ← depths
    if !nestOcc deps ctx.names ctx.nP hi w then
      return (.ordinary, (if nestOcc deps ctx.names ctx.nP hi e then w else e), st)
    match w with
    | .forallE _ a b _ =>
      if nestOcc deps ctx.names ctx.nP hi a then
        throwInvalid "nested positivity: non positive occurrence of the datatypes being declared"
      let (k, nb, st) ← nestPos j env ctx fuel prog (dep + 1) (kb + 1) (b.inst1I (← fvar dep a)) st
      pure (k, .forallE .anonymous a (← abstractLvl dep nb) .default, st)
    | _ =>
      let args := w.getAppArgs.toList
      match w.getAppFn with
      | .fvar id =>
        match lvlOf deps id with
        | some i =>
          match nestHoleAt ctx prog i with
          | some h =>
            if args.all (fun x => !nestOcc deps ctx.names ctx.nP hi x) &&
                args.length + h.key.ds.length == nestArity ctx h.key.cname then
              return (if i < ctx.hiAt 0 then
                  (if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP))
                else .inProgress, w, st)
            else throw nestNonValid
          | none => throw nestNonValid
        | none => throw nestNonValid
      | .const n us =>
        if ctx.names.contains n then throw nestNonValid
        let (k, st) ← nestCont ctx j env (nestPos j env ctx fuel) prog kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

/-- Twin of `nestHoles`. -/
def nestHoles (ctx : NestCtx) : M (Option (List Expr)) := do
  let mut hs : List Expr := []
  for mm in [0:ctx.names.length] do
    match indView? ctx.env (ctx.names.getD mm .anonymous) with
    | some iv =>
      match instPisWith ctx.params iv.cv.type with
      | some t => hs := hs ++ [← fvar (ctx.nP + mm) t]
      | none => return none
    | none => return none
  return some hs

/-- Twin of `nestRootCanon`. -/
def nestRootCanon (ctx : NestCtx) (cv : CV) : M (Option Expr) :=
  nestCanonCrest ctx.names (ctx.lps.map .param) ctx.nP
    (cv.type.instLvlParamsI cv.lps (ctx.lps.map .param))

/-- Twin of `Expr.piDomsOcc`. -/
def piDomsOcc (deps : Array Nat) (names : List Name) (lo hi : Nat) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, .forallE _ d b _ => nestOcc deps names lo hi d || piDomsOcc deps names lo hi n b
  | _ + 1, _ => false

/-- Twin of `nestUniformOk`. -/
def nestUniformOk (ctx : NestCtx) (cv : CV) : M Bool := do
  let deps ← depths
  if piDomsOcc deps ctx.names ctx.nP (ctx.hiAt 0) ctx.nP cv.type then return false
  match ← nestRootCanon ctx cv with
  | some crest => return !nestOcc (← depths) ctx.names 0 0 crest
  | none => return false

/-- Twin of `nestUniform`. -/
def nestUniform (ctx : NestCtx) (ctorss : List (List (CV × Nat))) : M Unit := do
  for cs in ctorss do
    for c in cs do
      unless ← nestUniformOk ctx c.1 do
        throwInvalid s!"invalid occurrence of a datatype being declared in the type of {c.1.name}: \
          it must be applied to the parameters and universe levels of the mutual declaration"

/-- Twin of `nestRoot`. -/
def nestRoot (j : Job) (env : Kernel.Environment) (ctx : NestCtx) (holes : List Expr) :
    List (List (CV × Nat)) → NestState → M (List (List (List NestFieldKind × Expr)) × NestState)
  | [], st => pure ([], st)
  | cs :: css, st => do
    let (o, st) ← nestCtors ctx j env (fun crest => nestPos j env ctx (whnfWalkFuel crest)) []
      (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.names holes cs st
    let (os, st) ← nestRoot j env ctx holes css st
    pure (o :: os, st)

/-- Twin of `nestSeedOf`. -/
def nestSeedOf (ctx : NestCtx) (holes : List Expr) (I : Name) (us : List Level) (ds : List Expr)
    (nPc : Nat) : M (NestKey × Nat) := do
  let sub ← nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP
  let ds' ← ds.mapM fun x => do
    replaceFVars (nestKeyMap ctx.params holes) (← replaceApps sub 0 ctx.nP x)
  return (⟨I, us, ds'⟩, nPc)

/-- Twin of `nestSeeds`. -/
def nestSeeds (j : Job) (env : Kernel.Environment) (ctx : NestCtx) :
    List (NestKey × Nat) → NestState → M NestState
  | [], st => pure st
  | (key, nPc) :: ks, st => do
    let F := key.ds.foldl (fun a d => max a (whnfWalkFuel d)) fuelSlack
    let (_, cty) ← nestInstType ctx (ctx.hiAt 0) key
    let (_, st) ← nestContKey ctx j env (nestPos j env ctx F) [] 0 key.cname key.lvls key.ds nPc cty st
    nestSeeds j env ctx ks st

/-- Twin of `BlockShape.nestCtx`/`blockNestCtx`. -/
def blockNestCtx (p : BlockShape) (cvTas : List CV) (env : Kernel.Environment) :
    M (NestCtx × List Expr) := do
  let cvTa0 ← unwrapOr cvTas.head? (.internal "direct rec: no type former")
  let pq ← unwrapOr (← openPis p.nP cvTa0.type 0) (.internal "direct rec: type former telescope")
  let ctx : NestCtx := ⟨p.memberNames, p.lps, p.nP, p.nIdxs, pq.1, p.resSort, env⟩
  let holes ← unwrapOr (← nestHoles ctx) (.internal "direct rec: a member is not a stored former")
  pure (ctx, holes)

/-- Twin of `checkAbsCtorSorts(All)`. -/
def checkAbsCtorSortsAll (j : Job) (env : Kernel.Environment) (ctx : NestCtx) :
    List (List (CV × Nat)) → List (List (List NestFieldKind × Expr)) → M Unit
  | cs :: css, os :: oss => do
    for (c, o) in cs.zip os do
      unless ← allLevelParamsDefined ctx.lps o.2 do
        throwInternal "direct rec: a positivity normal form outside the block's level parameters"
      let xq ← unwrapOr (← openPis c.2 o.2 (ctx.hiAt 0)) (.internal "direct rec: abstracted \
        constructor fields")
      let _ ← checkStructFieldSorts j env (Lvl.isZero ctx.sort) false ctx.sort (ctx.hiAt 0)
        xq.1.toArray [] c.2
    checkAbsCtorSortsAll j env ctx css oss
  | _, _ => pure ()

/-- Twin of `checkBlockPositivity`. -/
def checkBlockPositivity (j : Job) (env₁ : Kernel.Environment) (p : BlockShape) (cvTas : List CV)
    (ctorsAs : List (List (CV × Nat))) :
    M (List (List (List NestFieldKind)) × List (List Expr) × NestState) := do
  let (ctx, holes) ← blockNestCtx p cvTas env₁
  nestUniform ctx ctorsAs
  let (outs, st) ← nestRoot j env₁ ctx holes ctorsAs {}
  checkAbsCtorSortsAll j env₁ ctx ctorsAs outs
  pure (outs.map (·.map (·.1)), outs.map (·.map (·.2)), st)

end IC

end Lean.Kernel.InLean
