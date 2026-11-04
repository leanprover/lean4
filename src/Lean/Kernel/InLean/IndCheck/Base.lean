/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.IndGen

/-!
# InLean's inductive checker: the stored block and its vocabulary

Inductive declarations are checked by **con-leche's installer and checked
job**, on the constants an unverified generator (`Lean/Kernel/InLean/IndGen.lean`) produced
the way the official kernel would.  The generated constants are the
*stored block*, in con-leche's record shape (`SCI`, twin of
`ConLeche.ConstantInfo`'s `indInfo`/`ctorInfo`/`recInfo`), and the checked
job (`Lean/Kernel/InLean/IndCheck/*`) runs on them.

This file: the stored block's records, the expression vocabulary the
installer's functions need over InLean's interned free variables, the
recogniser (twin of `Kernel/Inductives/BlockParts.lean`) and the pinned
basis blocks (twin of `Kernel/Basis/{Eq,Nat,Empty,False,And}.lean`).

**Free variables by level.**  con-leche's free variable is a de Bruijn
level with its type (`.fvar i ty`); the installer builds them purely
(`openPisAtFvars`), tests them by level (`nestOcc`'s `lo ≤ i < hi`) and
abstracts them by level (`abstract1 i`).  InLean's are interned `(depth,
type)` pairs (`St.fvTab`), so building one is a state operation
(`mkFVar`) and every level test reads the interned depth.  Abstracting
level `i` maps every interned variable at depth `i` to one before
`Expr.abstractI`, which is con-leche's reading of `abstract1 i` (it
abstracts the level, whatever the annotation).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

namespace IC

/-! ## The stored block (con-leche's record shape) -/

/-- Twin of `ConLeche.ConstantVal`. -/
structure CV where
  name : Name
  lps : List Name
  type : Expr
  deriving Inhabited

/-- A stored recursor rule (the record's part: constructor, fields, rhs). -/
structure SRule where
  ctor : Name
  nfields : Nat
  rhs : Expr
  deriving Inhabited

/-- Twin of the three inductive kinds of `ConLeche.ConstantInfo`. -/
inductive SCI where
  | ind (cv : CV)
  | ctor (cv : CV) (nP nF : Nat)
  | recr (cv : CV) (mI rP : Nat) (rules : List SRule)
  deriving Inhabited

def SCI.cv : SCI → CV
  | .ind cv | .ctor cv .. | .recr cv .. => cv

def SCI.name (c : SCI) : Name := c.cv.name

def ofCI (ci : ConstantInfo) : CV := ⟨ci.name, ci.levelParams, ci.type⟩

/-- The generator's constants as a stored block, in the export's order
(formers, constructors, recursors). -/
def storedBlock (consts : Array ConstantInfo) : List SCI :=
  let inds := consts.filterMap fun
    | .inductInfo v => some (SCI.ind (ofCI (.inductInfo v)))
    | _ => none
  let ctors := consts.filterMap fun
    | .ctorInfo v => some (SCI.ctor (ofCI (.ctorInfo v)) v.numParams v.numFields)
    | _ => none
  let recs := consts.filterMap fun
    | .recInfo v => some (SCI.recr (ofCI (.recInfo v))
        (v.numParams + v.numMotives + v.numMinors + v.numIndices)
        (v.numParams + v.numMotives + v.numMinors)
        (v.rules.map fun r => ⟨r.ctor, r.nfields, r.rhs⟩))
    | _ => none
  (inds ++ ctors ++ recs).toList

/-! ## Free variables by level -/

/-- con-leche's `.fvar i ty`: the interned variable. -/
@[inline] def fvar (i : Nat) (ty : Expr) : M Expr := mkFVar i ty

/-- con-leche's `Expr.fvarTypeD`: an interned variable's type. -/
def fvarTypeD (x : Expr) : M Expr := do
  match x with
  | .fvar id =>
    match ← fvarInfo? id with
    | some (ty, _) => return ty
    | none => return default
  | _ => return default

/-- The depth snapshot the pure level tests read. -/
def depths : M (Array Nat) := do return (← get).fvDeps

def lvlOf (deps : Array Nat) (id : FVarId) : Option Nat :=
  match fvNum? id with
  | some n => deps[n]?
  | none => none

/-- con-leche's `openPisAtFvars n e i`: open `n` binders at the variables
of levels `i, i+1, …`, each typed by its instantiated domain. -/
def openPis (n : Nat) (e : Expr) (i : Nat) : M (Option (List Expr × Expr)) := do
  let mut e := e
  let mut fvs : Array Expr := #[]
  for k in [0:n] do
    match e with
    | .forallE _ dom body _ =>
      let fv ← fvar (i + k) dom
      fvs := fvs.push fv
      e := body.inst1I fv
    | _ => return none
  return some (fvs.toList, e)

/-- Every variable of `e` (not through annotations) at level `i`. -/
def fvarsAtLvl (deps : Array Nat) (i : Nat) (e : Expr) : Array FVarId :=
  (fvarsOf e).filter fun id => lvlOf deps id == some i

/-- con-leche's `e.abstract1 i 0`: the level-`i` variables to `bvar 0`. -/
def abstractLvl (i : Nat) (e : Expr) : M Expr := do
  if !e.hasFVar then return e
  let ids := fvarsAtLvl (← depths) i e
  if ids.isEmpty then return e
  let c : Expr := .fvar ids[0]!
  let e' := if ids.size == 1 then e else
    e.replaceI fun | .fvar id => if ids.contains id then some c else none | _ => none
  abstractChecked e' #[c]

/-- con-leche's `Expr.abstractPrefix k 0`: levels `0 … k-1` to `bvar (k-1)
… bvar 0`. -/
def abstractPrefix (k : Nat) (e : Expr) : M Expr := do
  if !e.hasFVar then return e
  let deps ← depths
  let ids := (fvarsOf e).filter fun id => match lvlOf deps id with
    | some d => d < k
    | none => false
  if ids.isEmpty then return e
  -- one representative per level, every variable of that level mapped to it
  let mut reps : Array (Option Expr) := Array.replicate k none
  for id in ids do
    if let some d := lvlOf deps id then
      if reps[d]!.isNone then reps := reps.set! d (some (.fvar id))
  let e' := e.replaceI fun
    | .fvar id => match lvlOf deps id with
      | some d => if d < k then reps[d]! else none
      | none => none
    | _ => none
  -- a level that does not occur gets a fresh, unused stand-in
  let mut xs : Array Expr := #[]
  for d in [0:k] do
    match reps[d]! with
    | some x => xs := xs.push x
    | none => xs := xs.push (.fvar ⟨.num `_inlean_absent d⟩)
  abstractChecked e' xs

/-- con-leche's `closeTelescope`. -/
def closeTelescope : List Expr → Nat → Expr → M Expr
  | [], _, body => pure body
  | dom :: bs, i, body => do
    let inner ← closeTelescope bs (i + 1) body
    return .forallE .anonymous dom (← abstractLvl i inner) .default

/-- con-leche's `closeLams`. -/
def closeLams : List Expr → Nat → Expr → M Expr
  | [], _, body => pure body
  | dom :: bs, i, body => do
    let inner ← closeLams bs (i + 1) body
    return .lam .anonymous dom (← abstractLvl i inner) .default

/-- The types of the variables reachable from `e` (hereditary). -/
def annotationsOf (e : Expr) : M (Array Expr) := do
  if !e.hasFVar then return #[]
  let s ← get
  return (← fvarClosure e).toArray.filterMap fun id =>
    match fvNum? id with
    | some n => s.fvTys[n]?
    | none => none

/-- con-leche's `Expr.mentionsAnyConst` (through annotations; a
projection names its structure). -/
def mentionsAnyConst (names : List Name) (e : Expr) : M Bool := do
  let p : Expr → Bool := fun
    | .const n _ => names.contains n
    | .proj s _ _ => names.contains s
    | _ => false
  if (e.findI? p).isSome then return true
  return (← annotationsOf e).any fun t => (t.findI? p).isSome

/-- con-leche's `Expr.nestOcc names lo hi`: a member constant, or a
variable of level in `[lo, hi)` (annotations not descended). -/
def nestOcc (deps : Array Nat) (names : List Name) (lo hi : Nat) (e : Expr) : Bool :=
  (e.findI? fun
    | .const n _ => names.contains n
    | .fvar id => match lvlOf deps id with
      | some i => lo ≤ i && i < hi
      | none => false
    | _ => false).isSome

def nestOccM (names : List Name) (lo hi : Nat) (e : Expr) : M Bool := do
  return nestOcc (← depths) names lo hi e

/-- con-leche's `Expr.fvarB`: one more than the largest level of a
variable reachable from `e` (hereditary), `0` for none. -/
def fvarB (e : Expr) : M Nat := do
  if !e.hasFVar then return 0
  let deps ← depths
  return (← fvarClosure e).fold (init := 0) fun acc id =>
    match lvlOf deps id with
    | some d => max acc (d + 1)
    | none => acc

/-- con-leche's `Expr.bvarB`. -/
@[inline] def bvarB (e : Expr) : Nat := e.looseBVarRange

/-- con-leche's `Expr.replaceFVars f` by level (annotations untouched). -/
def replaceFVars (f : Nat → Option Expr) (e : Expr) : M Expr := do
  if !e.hasFVar then return e
  let deps ← depths
  return e.replaceI fun
    | .fvar id => match lvlOf deps id with
      | some i => f i
      | none => none
    | _ => none

/-- con-leche's `Expr.eraseFVarTys`: every variable re-annotated `Sort 0`. -/
def eraseFVarTys (e : Expr) : M Expr := do
  if !e.hasFVar then return e
  let deps ← depths
  let mut m : Std.HashMap FVarId Expr := {}
  for id in fvarsOf e do
    if let some i := lvlOf deps id then
      m := m.insert id (← fvar i (.sort .zero))
  return e.replaceI fun
    | .fvar id => m[id]?
    | _ => none

/-- con-leche's `Expr.constsResolve` at an environment (through
annotations; literals need their support names). -/
def constsResolve (env : Kernel.Environment) (e : Expr) : M Bool := do
  let ok1 (t : Expr) : Bool :=
    (EO.usedConstants t).all (fun c => (env.find? c).isSome) &&
    (t.findI? fun
      | .proj s _ _ => (env.find? s).isNone
      | .lit (.natVal _) => !((env.find? natName).isSome && (env.find? natZeroName).isSome &&
          (env.find? natSuccName).isSome)
      | .lit (.strVal _) => !([natName, natZeroName, natSuccName, stringName, stringOfListName,
          listName, listNilName, listConsName, charName, charOfNatName].all fun n => (env.find? n).isSome)
      | _ => false).isNone
  if !ok1 e then return false
  return (← annotationsOf e).all ok1

/-- con-leche's `Expr.allLevelParamsDefined` (through annotations). -/
def allLevelParamsDefined (lps : List Name) (e : Expr) : M Bool := do
  let ok (t : Expr) : Bool := !t.hasLevelParam || (levelParamsOf t).all lps.contains
  if !ok e then return false
  return (← annotationsOf e).all ok

/-! ## Pure telescope readers (twins of `ExprOps.lean`'s) -/

/-- con-leche's `Expr.stripPis n`: the domains and the residual, raw. -/
def stripPis : Nat → Expr → Option (List Expr × Expr)
  | 0, e => some ([], e)
  | n + 1, .forallE _ d b _ => (stripPis n b).map fun (ds, r) => (d :: ds, r)
  | _ + 1, _ => none

/-- con-leche's `Expr.stripLams n`. -/
def stripLams : Nat → Expr → Option (List Expr × Expr)
  | 0, e => some ([], e)
  | n + 1, .lam _ d b _ => (stripLams n b).map fun (ds, r) => (d :: ds, r)
  | _ + 1, _ => none

/-- con-leche's `Expr.piBinders`. -/
def piBinders : Expr → List Expr × Expr
  | .forallE _ ty b _ => let (bs, e) := piBinders b; (ty :: bs, e)
  | e => ([], e)

/-- con-leche's `Expr.piSortTeleLen?`. -/
def piSortTeleLen? : Expr → Option Nat
  | .forallE _ _ b _ => (piSortTeleLen? b).map (· + 1)
  | .sort _ => some 0
  | _ => none

/-- con-leche's `instPisWith`. -/
def instPisWith : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ _ body _ => instPisWith as (body.inst1I a)
  | _ :: _, _ => none

/-- con-leche's `targetPiDomsWith`. -/
def targetPiDomsWith : List Expr → Expr → Option (List Expr)
  | [], _ => some []
  | x :: xs, .forallE _ d b _ => (d :: ·) <$> targetPiDomsWith xs (b.inst1I x)
  | _ :: _, _ => none

/-- con-leche's `Expr.mkPisOf`/`mkAppN` on lists. -/
def mkAppL (f : Expr) (args : List Expr) : Expr := mkAppN f args.toArray

/-- Pointwise alpha-equivalence (con-leche's list equality on its
name-free terms). -/
def listAlpha : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => EO.alphaEq a b && listAlpha as bs
  | _, _ => false

/-- `Level.isEquivList = some true`. -/
def lvlsEquiv : List Level → List Level → Bool
  | [], [] => true
  | l :: ls, r :: rs => Lvl.isEquiv l r == some true && lvlsEquiv ls rs
  | _, _ => false

def isNeverZero : Level → Bool := Ind.isNeverZero

/-- con-leche's `unwrapOr`. -/
def unwrapOr (o : Option α) (err : Err) : M α :=
  match o with
  | some a => pure a
  | none => throw err

/-- con-leche's `Name.nodup` on lists. -/
def nodup (ns : List Name) : Bool := namesNodup ns

/-! ## The environment's con-leche reading -/

/-- An inductive's reading as con-leche's `indInfo cv caps` exposes it:
the former, its parameter count, constructors and block. -/
structure IndView where
  cv : CV
  nparams : Nat
  ctors : List Name
  all : List Name

def indView? (env : Kernel.Environment) (n : Name) : Option IndView :=
  match env.find? n with
  | some ci@(.inductInfo v) => some ⟨ofCI ci, v.numParams, v.ctors, v.all⟩
  | _ => none

def ctorView? (env : Kernel.Environment) (n : Name) : Option (CV × Nat × Nat) :=
  match env.find? n with
  | some ci@(.ctorInfo v) => some (ofCI ci, v.numParams, v.numFields)
  | _ => none

/-! ## The recogniser (twin of `Inductives/BlockParts.lean`) -/

structure MemberShape where
  cvT : CV
  nIdx : Nat
  ctors : List (CV × Nat)
  deriving Inhabited

structure RecShape where
  cvR : CV
  rP : Nat
  mI : Nat
  tgt : Nat
  rules : List SRule
  deriving Inhabited

structure BlockShape where
  members : List MemberShape
  recs : List RecShape
  nP : Nat
  elim : Name
  resSort : Level
  large : Bool
  isProp : Bool
  deriving Inhabited

namespace BlockShape
def k (p : BlockShape) : Nat := p.members.length
def numCtors (p : BlockShape) : Nat := (p.members.map (·.ctors.length)).sum
def memberNames (p : BlockShape) : List Name := p.members.map (·.cvT.name)
def nIdxs (p : BlockShape) : List Nat := p.members.map (·.nIdx)
def lps (p : BlockShape) : List Name := (p.members.head?.map (·.cvT.lps)).getD []
def allCtors (p : BlockShape) : List (CV × Nat) := (p.members.map (·.ctors)).flatten
def rulePrefixAt (p : BlockShape) (r : Nat) : Nat := (p.recs.getD r default).rP
def majorIdxAt (p : BlockShape) (r : Nat) : Nat := (p.recs.getD r default).mI
def withSort (p : BlockShape) (s : Level) : BlockShape :=
  { p with resSort := s, isProp := Lvl.isZero s }
end BlockShape

def blockSplitRecs : List SCI → Option (List (CV × Nat × Nat × List SRule))
  | [] => some []
  | .recr cvR mI rP rules :: rest => (blockSplitRecs rest).map fun rs => (cvR, mI, rP, rules) :: rs
  | _ => none

def blockSplitCtors : List SCI → Option (List (CV × Nat × Nat) × List (CV × Nat × Nat × List SRule))
  | .ctor cvC nP nF :: rest => (blockSplitCtors rest).map fun q => ((cvC, nP, nF) :: q.1, q.2)
  | rest => (blockSplitRecs rest).map fun rs => ([], rs)

def blockSplit : List SCI →
    Option (List CV × List (CV × Nat × Nat) × List (CV × Nat × Nat × List SRule))
  | .ind cvT :: rest => (blockSplit rest).map fun q => (cvT :: q.1, q.2)
  | rest => (blockSplitCtors rest).map fun q => ([], q.1, q.2)

def recTargetOf (names : List Name) (mI : Nat) (ty : Expr) : Nat :=
  match stripPis mI ty with
  | some (_, .forallE _ dom _ _) =>
    (match dom.getAppFn with
     | .const n _ => names.findIdx? (· == n)
     | _ => none).getD names.length
  | _ => names.length

def blockCounts? (nPd k nC nR : Nat) (cvT : CV) (r : Option (Nat × Nat)) : Option (Nat × Nat) :=
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

def memberIdxAt? (names : List Name) (lvls : List Level) : Expr → Option Nat
  | .const n us => if us == lvls then names.findIdx? (· == n) else none
  | _ => none

def ctorMember? (names : List Name) (lps : List Name) (nP : Nat) (c : CV × Nat) : Option Nat :=
  match stripPis (nP + c.2) c.1.type with
  | some (_, cbody) => memberIdxAt? names (lps.map .param) cbody.getAppFn
  | none => none

def blockGroups (names : List Name) (lps : List Name) (nP k : Nat) (cs : List (CV × Nat)) :
    List (List (CV × Nat)) :=
  if k == 1 then [cs]
  else (List.range k).map fun m => cs.filter fun c => ctorMember? names lps nP c == some m

/-- Twin of `reservedRecName` (`CoreDefs.lean`). -/
def reservedRecName (n : Name) : Bool :=
  reservedBasisNames.contains n ||
    [natName, natZeroName, natSuccName, stringName, stringOfListName, listName, listNilName,
     listConsName, charName, charOfNatName].contains n ||
    natOpNames.contains n || natDivModNames.contains n ||
    n == boolName || n == boolTrueName || n == boolFalseName

def blockRecLpsOk (p : BlockShape) : Bool :=
  p.recs.all fun rc =>
    if p.large then rc.cvR.lps == p.elim :: p.lps else rc.cvR.lps == p.lps

def blockRecNameSetOk (p : BlockShape) : Bool :=
  let want := p.members.map fun ms => ms.cvT.name.str "rec"
  let got := p.recs.map fun rc => rc.cvR.name
  got.length == want.length && want.all (fun n => got.contains n) && got.all (fun n => want.contains n)

def blockRecNamesUnreserved (p : BlockShape) : Bool :=
  p.recs.all fun rc => reservedRecName rc.cvR.name == false

def blockMemberCounts? (nPd k nC : Nat) (names : List Name) (rs : List (CV × Nat × Nat × List SRule)) :
    Nat → List CV → Option (List Nat)
  | _, [] => some []
  | m, cvT :: ts =>
    let r := (rs.find? fun q => recTargetOf names q.2.1 q.1.type == m).map fun q => (q.2.1, q.2.2.1)
    match blockCounts? nPd k nC rs.length cvT r with
    | some c => (blockMemberCounts? nPd k nC names rs (m + 1) ts).map fun ns => c.2 :: ns
    | none => none

/-- Twin of `blockShape?`/`blockParts?`. -/
def blockParts? (nPd : Nat) (block : List SCI) : Option BlockShape :=
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    match cvTs, rs with
    | cvT0 :: _, (cvR0, _, _, _) :: _ =>
      let lps := cvT0.lps
      let names := cvTs.map (·.name)
      let k := cvTs.length
      match blockMemberCounts? nPd k cs.length names rs 0 cvTs with
      | none => none
      | some nIdxs =>
        let nP := nPd
        if (cvTs.all fun c => !reservedBasisNames.contains c.name) &&
            (rs.all fun r => !reservedBasisNames.contains r.1.name) &&
            (cvTs.all fun c => c.lps == lps) &&
            cs.all (fun c => c.2.1 == nP && c.1.lps == lps && !reservedBasisNames.contains c.1.name) then
          let s : Level := match stripPis (nP + nIdxs.headD 0) cvT0.type with
            | some (_, .sort s) => s
            | _ => .zero
          let isProp := Lvl.isZero s
          let ctors : List (CV × Nat) := cs.map fun c => (c.1, c.2.2)
          let groups := blockGroups names lps nP k ctors
          let members := ((cvTs.zip nIdxs).zip groups).map fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape)
          let recsL := rs.map fun r =>
            (⟨r.1, r.2.2.1, r.2.1, recTargetOf names r.2.1 r.1.type, r.2.2.2⟩ : RecShape)
          let large? : Option Name := match cvR0.lps with
            | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
            | [] => none
          match large? with
          | some elim => some ⟨members, recsL, nP, elim, s, true, isProp⟩
          | none => some ⟨members, recsL, nP, .anonymous, s, false, isProp⟩
        else none
    | _, _ => none
  | none => none

/-- Twin of `indParamsOk`. -/
def indParamsOk (nP : Nat) (block : List SCI) : Bool :=
  block.all fun
    | .ind cvT => match piSortTeleLen? cvT.type with
      | some n => nP ≤ n
      | none => true
    | .ctor _ nPc _ => nPc == nP
    | _ => true

/-- Twin of `blockRawRec` (official's `is_rec`, syntactic). -/
def blockRawRec (p : BlockShape) : M Bool := do
  for ms in p.members do
    for c in ms.ctors do
      let mut t := c.1.type
      while t.isForall do
        if ← mentionsAnyConst p.memberNames t.bindingDomain! then return true
        t := t.bindingBody!
  return false

/-! ## The pinned basis blocks (twin of `Kernel/Basis/*`, compared up to `canon`) -/

open BasisDSL in
/-- The pinned blocks: names, types, and the recursors' counts and rules. -/
def basisPins : List (List SCI) :=
  let eqT := cnst eqName [u]
  let eqRecMotive := pi "b" (bv 1) <| pi "t" (ap3 eqT (bv 2) (bv 1) (bv 0)) (srt u1)
  let natT := cnst natName
  let natRecMotive := pi "t" natT (srt u)
  let natRecSucc := pi "n" natT <| pi "n_ih" (.app (bv 2) (bv 0)) <|
    .app (bv 3) (.app (cnst natSuccName) (bv 1))
  [ -- Eq
    [.ind ⟨eqName, [uN], piI "α" (srt u) <| pi "a" (bv 0) <| pi "b" (bv 1) prop⟩,
     .ctor ⟨eqReflName, [uN], piI "α" (srt u) <| pi "a" (bv 0) <| ap3 eqT (bv 1) (bv 0) (bv 0)⟩ 2 0,
     .recr ⟨eqRecName, [u1N, uN],
        piI "α" (srt u) <| piI "a" (bv 0) <| piI "motive" eqRecMotive <|
        pi "refl" (ap2 (bv 0) (bv 1) (ap2 (cnst eqReflName [u]) (bv 2) (bv 1))) <|
        piI "b" (bv 3) <| pi "t" (ap3 eqT (bv 4) (bv 3) (bv 0)) <| ap2 (bv 3) (bv 1) (bv 0)⟩ 5 4
        [⟨eqReflName, 0, lmI "α" (srt u) <| lm "a" (bv 0) <| lm "motive" eqRecMotive <|
          lm "refl" (ap2 (bv 0) (bv 1) (ap2 (cnst eqReflName [u]) (bv 2) (bv 1))) <| bv 0⟩]],
    -- Nat
    [.ind ⟨natName, [], type1⟩,
     .ctor ⟨natZeroName, [], natT⟩ 0 0,
     .ctor ⟨natSuccName, [], pi "n" natT natT⟩ 0 1,
     .recr ⟨natName.str "rec", [uN],
        piI "motive" natRecMotive <| pi "zero" (.app (bv 0) (cnst natZeroName)) <|
        pi "succ" natRecSucc <| pi "t" natT (.app (bv 3) (bv 0))⟩ 3 3
        [⟨natZeroName, 0, lm "motive" natRecMotive <| lm "zero" (.app (bv 0) (cnst natZeroName)) <|
           lm "succ" natRecSucc <| bv 1⟩,
         ⟨natSuccName, 1, lm "motive" natRecMotive <| lm "zero" (.app (bv 0) (cnst natZeroName)) <|
           lm "succ" natRecSucc <| lm "n" natT <|
           ap2 (bv 1) (bv 0) (ap4 (cnst (natName.str "rec") [u]) (bv 3) (bv 2) (bv 1) (bv 0))⟩]],
    -- Empty
    [.ind ⟨`Empty, [], type1⟩,
     .recr ⟨`Empty.rec, [uN], pi "motive" (pi "t" (cnst `Empty) (srt u)) <|
        pi "t" (cnst `Empty) (.app (bv 1) (bv 0))⟩ 1 1 []],
    -- False
    [.ind ⟨`False, [], prop⟩,
     .recr ⟨`False.rec, [uN], pi "motive" (pi "t" (cnst `False) (srt u)) <|
        pi "t" (cnst `False) (.app (bv 1) (bv 0))⟩ 1 1 []]]

open BasisDSL in
/-- The pinned `And` (twin of `Basis/And.lean`). -/
def andPin : List SCI :=
  let andRecMotive := pi "t" (ap2 (cnst andName) (bv 1) (bv 0)) (srt u)
  let andRecMinor := pi "left" (bv 2) <| pi "right" (bv 2) <|
    .app (bv 2) (ap4 (cnst andIntroName) (bv 4) (bv 3) (bv 1) (bv 0))
  [.ind ⟨andName, [], pi "a" prop (pi "b" prop prop)⟩,
   .ctor ⟨andIntroName, [], piI "a" prop <| piI "b" prop <| pi "left" (bv 1) <| pi "right" (bv 1) <|
      ap2 (cnst andName) (bv 3) (bv 2)⟩ 2 2,
   .recr ⟨`And.rec, [uN], piI "a" prop <| piI "b" prop <| piI "motive" andRecMotive <|
      pi "intro" andRecMinor <| pi "t" (ap2 (cnst andName) (bv 3) (bv 2)) <| .app (bv 2) (bv 0)⟩ 4 4
      [⟨andIntroName, 2, lmI "a" prop <| lmI "b" prop <| lmI "motive" andRecMotive <|
        lm "intro" andRecMinor <| lm "left" (bv 3) <| lm "right" (bv 3) <| ap2 (bv 2) (bv 1) (bv 0)⟩]]

/-- Twin of `ConstantInfo.canonEq` on the stored block's records:
level parameters renamed positionally, `mdata` stripped,
alpha-equivalence. -/
def canonEq (a b : SCI) : Bool :=
  let cvEq (x y : CV) : Bool :=
    x.name == y.name && x.lps.length == y.lps.length &&
      EO.alphaEq (canonAt x.lps y.lps x.type) y.type
  match a, b with
  | .ind x, .ind y => cvEq x y
  | .ctor x nP nF, .ctor y nP' nF' => cvEq x y && nP == nP' && nF == nF'
  | .recr x mI rP rs, .recr y mI' rP' rs' =>
    cvEq x y && mI == mI' && rP == rP' && rs.length == rs'.length &&
      (rs.zip rs').all fun (r, r') =>
        r.ctor == r'.ctor && r.nfields == r'.nfields && EO.alphaEq (canonAt x.lps y.lps r.rhs) r'.rhs
  | _, _ => false

def canonEqList (xs ys : List SCI) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (a, b) => canonEq a b

/-- Twin of `basisPinHit`. -/
def basisPinHit (block : List SCI) : Bool :=
  match basisPins.find? fun pin => pin.map (·.name) == block.map (·.name) with
  | some pin => canonEqList block pin
  | none => false

/-- Twin of `andPinOk` at an inductive block. -/
def andPinOk (nP : Nat) (block : List SCI) : Bool :=
  !(block.any fun c => [andName, andIntroName, `And.rec].contains c.name) ||
    (nP == 2 && canonEqList block andPin)

end IC

end Lean.Kernel.InLean
