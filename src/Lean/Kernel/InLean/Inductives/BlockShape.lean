/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.CheckerC

/-!
# InLean's inductive check: the vocabulary and the recogniser

Twins of `ConLeche/Kernel/Inductives/BlockShape.lean` (the block's
recogniser and its records), the parts of `FieldTele.lean`,
`Positivity.lean` and `ConLeche/Kernel/ExprOps.lean` the block check reads
(telescopes, the free-variable walks), and `CheckerOps`.

A block is a list of Lean constants (`inductInfo`, `ctorInfo`, `recInfo`, in
that order), the twin of the stream's records: the inductive generator's
output (`Lean/Kernel/InLean/IndGen.lean`).

**Free variables.**  con-leche builds `.fvar i ty` purely; here building one
interns it (`mkFVarM`), so a function that opens a telescope is in `CheckCM`.
A walk that reads a variable's level reads the id (`EO.fvDepth?`) and stays
pure; a walk that descends into a variable's type (con-leche's node carries
it) reads the state's type table (`fvTyOf`).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## The operations -/

/-- Twin of `CheckerOps CheckCM`: the core's entry points at an environment. -/
structure CheckerOps where
  inferType : FEnv → Nat → Expr → CheckCM Expr
  isDefEq : FEnv → Nat → Expr → Expr → CheckCM Bool
  ensureSort : FEnv → Nat → Expr → CheckCM Level
  whnf : FEnv → Nat → Expr → CheckCM Expr

/-- Twin of `unwrapOr`. -/
def unwrapOr (o : Option α) (err : CheckError) : CheckCM α :=
  match o with
  | some a => pure a
  | none => throw err

/-! ## Telescopes -/

/-- Twin of `Expr.stripPis`: the first `n` binder domains, raw, and the rest. -/
def stripPis : Nat → Expr → Option (List Expr × Expr)
  | 0, e => some ([], e)
  | n + 1, .forallE _ d b _ => (stripPis n b).map fun (ds, r) => (d :: ds, r)
  | _ + 1, _ => none

/-- Twin of `Expr.stripLams`. -/
def stripLams : Nat → Expr → Option (List Expr × Expr)
  | 0, e => some ([], e)
  | n + 1, .lam _ d b _ => (stripLams n b).map fun (ds, r) => (d :: ds, r)
  | _ + 1, _ => none

/-- Twin of `Expr.piBinders`. -/
def piBinders : Expr → List Expr × Expr
  | .forallE _ ty b _ =>
    let (bs, e) := piBinders b
    (ty :: bs, e)
  | e => ([], e)

/-- Twin of `Expr.mkPisOf`. -/
def mkPisOf : List Expr → Expr → Expr
  | [], body => body
  | ty :: bs, body => .forallE .anonymous ty (mkPisOf bs body) .default

/-- Twin of `instPisWith`. -/
def instPisWith : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ _ body _ => instPisWith as (body.inst1I a)
  | _ :: _, _ => none

/-- Twin of `Expr.instPisAtLift`. -/
def instPisAtLift : List Expr → Expr → Option Expr := instPisWith

/-- Twin of `targetPiDomsWith`. -/
def targetPiDomsWith : List Expr → Expr → Option (List Expr)
  | [], _ => some []
  | x :: xs, .forallE _ d b _ => (d :: ·) <$> targetPiDomsWith xs (b.inst1I x)
  | _ :: _, _ => none

/-- Twin of `Expr.mkAppN` on a list. -/
@[inline] def mkAppL (f : Expr) (args : List Expr) : Expr := mkAppN f args.toArray

/-! ## Free variables -/

/-- Twin of `openPisAtFvars`: the first `n` binders opened at the variables of
depths `i, i + 1, …`. -/
def openPisAtFvars : Nat → Expr → Nat → CheckCM (Option (List Expr × Expr)) :=
  openPisAtFvarsM

/-- Twin of `Expr.fvarTypeD`. -/
def fvarTypeD (x : Expr) : CheckCM Expr := do
  match x with
  | .fvar id => return (← fvarTypeM? id).getD default
  | _ => return default

/-- Twin of `Expr.fvarB`: one more than the largest depth of a variable in `e`
(the variables' types not descended). -/
def fvarB (e : Expr) : Nat :=
  if !e.hasFVar then 0 else
  (EO.fvarIds e).foldl (init := 0) fun acc id =>
    match EO.fvDepth? id with
    | some d => max acc (d + 1)
    | none => acc

/-- Twin of `Expr.nestOcc names lo hi`: a member constant, or a variable of
level in `[lo, hi)` (types not descended). -/
def nestOcc (names : List Name) (lo hi : Nat) (e : Expr) : Bool :=
  EO.any (fun
    | .const n _ => names.contains n
    | .fvar id => match EO.fvDepth? id with
      | some i => lo ≤ i && i < hi
      | none => false
    | _ => false) e

/-- Twin of `Expr.replaceFVars f`: the variable of level `i` to `f i` (types
not descended). -/
def replaceFVars (f : Nat → Option Expr) (e : Expr) : Expr :=
  if !e.hasFVar then e else
  EO.replace (fun
    | .fvar id => match EO.fvDepth? id with
      | some i => f i
      | none => none
    | x => if x.hasFVar then none else some x) e

/-- Twin of `e.abstract1 i c`: the variables of level `i` to `bvar c` (at
binder offset `c`). -/
def abstract1 (e : Expr) (i c : Nat) : Expr := EO.abstractDepthsFrom e i 1 c

/-- Twin of `closeTelescope`. -/
def closeTelescope : List Expr → Nat → Expr → Expr
  | [], _, body => body
  | dom :: bs, i, body =>
    .forallE .anonymous dom (abstract1 (closeTelescope bs (i + 1) body) i 0) .default

/-- Twin of `closeLams`. -/
def closeLams : List Expr → Nat → Expr → Expr
  | [], _, body => body
  | dom :: bs, i, body =>
    .lam .anonymous dom (abstract1 (closeLams bs (i + 1) body) i 0) .default

/-- Twin of `Expr.abstractPrefix`. -/
def abstractPrefix : Nat → Nat → Expr → Expr
  | 0, _, e => e
  | k + 1, c, e => abstractPrefix k (c + 1) (abstract1 e k c)

/-- The terms a term reads: itself and the types of the variables reachable
from it (con-leche's walks descend into a variable's type annotation). -/
def withAnnotations (e : Expr) : CheckCM (List Expr) := do
  if !e.hasFVar then return [e]
  let tys := (← get).fvTys
  let ids ← fvarClosureM e
  return e :: ids.toList.filterMap (fvTyOf tys)

/-- Twin of `Expr.mentionsAnyConst` (through annotations; a projection names
its structure). -/
def mentionsAnyConst (names : List Name) (e : Expr) : CheckCM Bool := do
  let p : Expr → Bool := fun
    | .const n _ => names.contains n
    | .proj s _ _ => names.contains s
    | _ => false
  return (← withAnnotations e).any (EO.any p)

/-- Twin of `Expr.constsResolveF` (through annotations; a literal needs its
support names). -/
def constsResolveF (fe : FEnv) (e : Expr) : CheckCM Bool := do
  let ok (t : Expr) : Bool :=
    (EO.usedConstants t).all (fun c => (fe.find? c).isSome) &&
    !EO.any (fun
      | .proj s _ _ => (fe.find? s).isNone
      | .lit (.natVal _) => !natLitStoredF fe
      | .lit (.strVal _) => !strLitStoredF fe
      | _ => false) t
  return (← withAnnotations e).all ok

/-- Twin of `Expr.allLevelParamsDefined` (through annotations). -/
def allLevelParamsDefined (lps : List Name) (e : Expr) : CheckCM Bool := do
  return (← withAnnotations e).all fun t =>
    !t.hasLevelParam || (EO.levelParams t).all lps.contains

/-- Twin of `Expr.eraseFVarTys`: every variable re-annotated `Sort 0`. -/
def eraseFVarTys (e : Expr) : CheckCM Expr := do
  if !e.hasFVar then return e
  let mut m : Std.HashMap FVarId Expr := {}
  for id in EO.fvarIds e do
    if let some i := EO.fvDepth? id then
      m := m.insert id (← mkFVarM i (.sort .zero))
  return EO.replace (fun | .fvar id => m[id]? | _ => none) e

/-! ## Names -/

/-- Twin of `litGuardNames`. -/
def litGuardNames : List Name :=
  [natName, natZeroName, natSuccName, stringName, stringOfListName, listName, listNilName,
   listConsName, charName, charOfNatName]

/-- Twin of `reservedRecName`. -/
def reservedRecName (n : Name) : Bool :=
  reservedBasisNames.contains n || litGuardNames.contains n ||
    natOpNames.contains n || natDivModNames.contains n ||
    n == boolName || n == boolTrueName || n == boolFalseName

/-- Twin of `memberIdxAt?`. -/
def memberIdxAt? (names : List Name) (lvls : List Level) : Expr → Option Nat
  | .const n us => if us == lvls then names.findIdx? (· == n) else none
  | _ => none

/-! ## The record (twin of `BlockShape.lean`) -/

/-- Twin of `MemberShape`. -/
structure MemberShape where
  cvT : ConstantVal
  declared : ConstantVal
  nIdx : Nat
  ctors : List (ConstantVal × Nat)
  deriving Inhabited

/-- Twin of `RecShape`. -/
structure RecShape where
  cvR : ConstantVal
  rP : Nat
  mI : Nat
  tgt : Nat
  rules : List RecursorRule
  isK : Bool := false
  deriving Inhabited

/-- Twin of `MemberShape.structCtor?`. -/
def MemberShape.structCtor? (ms : MemberShape) : Option (ConstantVal × Nat) :=
  match ms.ctors with
  | [c] => if ms.nIdx == 0 then some c else none
  | _ => none

/-- Twin of `BlockShape`. -/
structure BlockShape where
  members : List MemberShape
  recs : List RecShape
  nP : Nat
  elim : Name
  resSort : Level
  large : Bool
  isProp : Bool
  deriving Inhabited

/-- Twin of `BlockShape.formers`. -/
def BlockShape.formers (p : BlockShape) : List ConstantVal := p.members.map (·.cvT)

/-- Twin of `BlockShape.memberCtors`. -/
def BlockShape.memberCtors (p : BlockShape) : List (List (ConstantVal × Nat)) :=
  p.members.map (·.ctors)

/-- Twin of `numCtorsOf`. -/
def numCtorsOf : List MemberShape → Nat
  | [] => 0
  | ms :: rest => ms.ctors.length + numCtorsOf rest

namespace BlockShape

def k (p : BlockShape) : Nat := p.members.length
def numCtors (p : BlockShape) : Nat := numCtorsOf p.members
def memberNames (p : BlockShape) : List Name := p.members.map (·.cvT.name)
def nIdxs (p : BlockShape) : List Nat := p.members.map (·.nIdx)
def lps (p : BlockShape) : List Name := (p.members.head?.map (·.cvT.levelParams)).getD []
def allCtors (p : BlockShape) : List (ConstantVal × Nat) := (p.members.map (·.ctors)).flatten
def recTgtAt (p : BlockShape) (r : Nat) : Nat := (p.recs.getD r default).tgt
def rulePrefixAt (p : BlockShape) (r : Nat) : Nat := (p.recs.getD r default).rP
def majorIdxAt (p : BlockShape) (r : Nat) : Nat := (p.recs.getD r default).mI

/-- Twin of `BlockShape.withSort`. -/
def withSort (p : BlockShape) (s : Level) : BlockShape :=
  { p with resSort := s, isProp := Lvl.isEquiv s .zero == some true }

end BlockShape

/-! ## Recognition -/

/-- A recursor record's parts: constant, `mI`, `rP`, K flag, rules. -/
abbrev RecParts := ConstantVal × Nat × Nat × Bool × List RecursorRule

/-- Twin of `blockSplitRecs`. -/
def blockSplitRecs : List ConstantInfo → Option (List RecParts)
  | [] => some []
  | .recInfo v :: rest =>
    (blockSplitRecs rest).map fun rs =>
      (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules) :: rs
  | _ => none

/-- Twin of `blockSplitCtors`. -/
def blockSplitCtors : List ConstantInfo →
    Option (List (ConstantVal × Nat × Nat) × List RecParts)
  | .ctorInfo v :: rest =>
    (blockSplitCtors rest).map fun q => ((v.toConstantVal, v.numParams, v.numFields) :: q.1, q.2)
  | rest => (blockSplitRecs rest).map fun rs => ([], rs)

/-- Twin of `blockSplit`. -/
def blockSplit : List ConstantInfo →
    Option (List ConstantVal × List (ConstantVal × Nat × Nat) × List RecParts)
  | .inductInfo v :: rest => (blockSplit rest).map fun q => (v.toConstantVal :: q.1, q.2)
  | rest => (blockSplitCtors rest).map fun q => ([], q.1, q.2)

/-- Twin of `recTargetOf`. -/
def recTargetOf (names : List Name) (mI : Nat) (ty : Expr) : Nat :=
  match stripPis mI ty with
  | some (_, .forallE _ dom _ _) =>
    (match dom.getAppFn with
     | .const n _ => names.findIdx? (· == n)
     | _ => none).getD names.length
  | _ => names.length

/-- Twin of `blockCounts?`. -/
def blockCounts? (nPd k nC nR : Nat) (cvT : ConstantVal) (r : Option (Nat × Nat)) :
    Option (Nat × Nat) :=
  match piBinders cvT.type with
  | (bs, .sort _) => if nPd ≤ bs.length then some (nPd, bs.length - nPd) else none
  | _ =>
    match r with
    | none => none
    | some (mI, rP) =>
      if rP < nC + k || mI < rP then none
      else if rP - (nC + k) == nPd then some (nPd, mI - rP)
      else if k < nR && nPd + nR + nC ≤ rP then some (nPd, mI - rP)
      else none

/-- Twin of `ctorMember?`. -/
def ctorMember? (names : List Name) (lps : List Name) (nP : Nat) (c : ConstantVal × Nat) :
    Option Nat :=
  match stripPis (nP + c.2) c.1.type with
  | some (_, cbody) => memberIdxAt? names (lps.map .param) cbody.getAppFn
  | none => none

/-- Twin of `blockGroups`. -/
def blockGroups (names : List Name) (lps : List Name) (nP k : Nat)
    (cs : List (ConstantVal × Nat)) : List (List (ConstantVal × Nat)) :=
  if k == 1 then [cs]
  else (List.range k).map fun m => cs.filter fun c => ctorMember? names lps nP c == some m

/-- Twin of `blockRecLpsOk`. -/
def blockRecLpsOk (p : BlockShape) : Bool :=
  p.recs.all fun rc =>
    if p.large then rc.cvR.levelParams == p.elim :: p.lps
    else rc.cvR.levelParams == p.lps

/-- Twin of `blockRecNameSetOk`. -/
def blockRecNameSetOk (p : BlockShape) : Bool :=
  let want := p.members.map fun ms => ms.cvT.name.str "rec"
  let got := p.recs.map fun rc => rc.cvR.name
  got.length == want.length && want.all (fun n => got.contains n) && got.all (fun n => want.contains n)

/-- Twin of `blockRecNamesUnreserved`. -/
def blockRecNamesUnreserved (p : BlockShape) : Bool :=
  p.recs.all fun rc => reservedRecName rc.cvR.name == false

/-- Twin of `blockMemberCounts?`. -/
def blockMemberCounts? (nPd k nC : Nat) (names : List Name) (rs : List RecParts) :
    Nat → List ConstantVal → Option (List Nat)
  | _, [] => some []
  | m, cvT :: ts =>
    let r := (rs.find? fun q => recTargetOf names q.2.1 q.1.type == m).map
      fun q => (q.2.1, q.2.2.1)
    match blockCounts? nPd k nC rs.length cvT r with
    | some c => (blockMemberCounts? nPd k nC names rs (m + 1) ts).map fun ns => c.2 :: ns
    | none => none

/-- Twin of `blockShape?`. -/
def blockShape? (nPd : Nat) (block : List ConstantInfo) : Option BlockShape :=
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    match cvTs, rs with
    | cvT0 :: _, (cvR0, _, _, _) :: _ =>
      let lps := cvT0.levelParams
      let names := cvTs.map (·.name)
      let k := cvTs.length
      match blockMemberCounts? nPd k cs.length names rs 0 cvTs with
      | none => none
      | some nIdxs =>
        let nP := nPd
        if (cvTs.all fun c => reservedBasisNames.contains c.name == false) &&
            (rs.all fun r => reservedBasisNames.contains r.1.name == false) &&
            (cvTs.all fun c => c.levelParams == lps) &&
            cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
              reservedBasisNames.contains c.1.name == false) then
          let s : Level := match stripPis (nP + nIdxs.headD 0) cvT0.type with
            | some (_, .sort s) => s
            | _ => .zero
          let isProp := Lvl.isEquiv s .zero == some true
          let ctors : List (ConstantVal × Nat) := cs.map fun c => (c.1, c.2.2)
          let groups := blockGroups names lps nP k ctors
          let members := ((cvTs.zip nIdxs).zip groups).map fun a =>
            ({ cvT := a.1.1, declared := a.1.1, nIdx := a.1.2, ctors := a.2 } : MemberShape)
          let recsL := rs.map fun r =>
            ({ cvR := r.1, rP := r.2.2.1, mI := r.2.1, tgt := recTargetOf names r.2.1 r.1.type,
               rules := r.2.2.2.2, isK := r.2.2.2.1 } : RecShape)
          let large? : Option Name :=
            match cvR0.levelParams with
            | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
            | [] => none
          match large? with
          | some elim => some ⟨members, recsL, nP, elim, s, true, isProp⟩
          | none => some ⟨members, recsL, nP, .anonymous, s, false, isProp⟩
        else none
    | _, _ => none
  | none => none

/-- Twin of `Expr.piSortTeleLen?`. -/
def piSortTeleLen? : Expr → Option Nat
  | .forallE _ _ body _ => (piSortTeleLen? body).map (· + 1)
  | .sort _ => some 0
  | _ => none

/-- Twin of `indParamsOk`. -/
def indParamsOk (nP : Nat) (block : List ConstantInfo) : Bool :=
  block.all fun
    | .inductInfo v => (piSortTeleLen? v.type).all (nP ≤ ·)
    | .ctorInfo v => v.numParams == nP
    | _ => true

end Lean.Kernel.InLean
