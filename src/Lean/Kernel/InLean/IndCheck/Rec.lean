/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.IndCheck.Positivity

/-!
# InLean's inductive checker: the recursors

Twins of `Kernel/Inductives/ClassRead.lean` (the
classes read off the stored recursors' types), `RecCheck.lean` (the
recursor targets), `GenRec.lean` (the regeneration of every recursor
type and rule, `genRecCheck`) and `StoredRecs.lean` (the stored
recursors against the regenerated ones, up to definitional equality).
The stored recursors are the generator's; binder names play no part on
this side.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

namespace IC

/-! ## The classes (twin of `ClassRead.lean`) -/

structure ClassKey where
  ind : Name
  lvls : List Level
  ds : List Expr
  deriving Inhabited

inductive ClassSlot where
  | motive (key : ClassKey)
  | minor (cls : Nat) (ctor : Name) (ihs : List (Nat × Nat))
  deriving Inhabited

def ClassSlot.isMinor : ClassSlot → Bool
  | .minor .. => true
  | .motive _ => false

structure ClassRead where
  slots : List ClassSlot
  recCls : List Nat
  deriving Inhabited

def ClassRead.classes (r : ClassRead) : List ClassKey :=
  r.slots.filterMap fun | .motive k => some k | _ => none

def ClassRead.motiveSlot (r : ClassRead) (c : Nat) : Option Nat :=
  let ms := (List.range r.slots.length).filter fun s =>
    match r.slots[s]? with | some (.motive _) => true | _ => false
  ms[c]?

def classOfMotiveVar (nP : Nat) (motPos : List Nat) (p : Nat) : Option Nat :=
  if nP ≤ p then motPos.findIdx? (· == p - nP) else none

/-- The level of a variable head. -/
def headLvl (deps : Array Nat) (e : Expr) : Option Nat :=
  match e.getAppFn with
  | .fvar id => lvlOf deps id
  | _ => none

/-- Twin of `classReadMinor`. -/
def classReadMinor (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) : M (Option ClassSlot) := do
  let n := (piBinders dom).1.length
  let some (fvs, concl) ← openPis n dom d | return none
  let deps ← depths
  let some p := headLvl deps concl | return none
  let some c := classOfMotiveVar nP motPos p | return none
  let some last := concl.getAppArgs.back? | return none
  let .const C _ := last.getAppFn | return none
  let mut ihs : List (Nat × Nat) := []
  for q in [0:fvs.length] do
    let fty ← fvarTypeD (fvs.getD q default)
    let res := piResult fty
    match headLvl deps res with
    | some p' =>
      match classOfMotiveVar nP motPos p' with
      | some t =>
        match res.getAppArgs.back? with
        | some a =>
          match headLvl deps a with
          | some f => if d ≤ f then ihs := ihs ++ [(f - d, t)]
          | none => pure ()
        | none => pure ()
      | none => pure ()
    | none => pure ()
  return some (.minor c C ihs)

/-- Twin of `classReadSlots`. -/
def classReadSlots (nPc : Name → Nat) (np : Nat) :
    Nat → List Nat → Nat → Expr → M (Option (List ClassSlot))
  | 0, _, _, _ => pure (some [])
  | n + 1, motPos, d, .forallE _ dom body _ => do
    let slot? : Option ClassSlot ← match piResult dom with
      | .sort _ => do
        let (bs, _) := piBinders dom
        match bs.getLast? with
        | some mdom =>
          match mdom.getAppFn with
          | .const I us => pure (some (ClassSlot.motive ⟨I, us, mdom.getAppArgs.toList.take (nPc I)⟩))
          | _ => pure none
        | none => pure none
      | _ => classReadMinor np motPos d dom
    let some slot := slot? | return none
    let motPos' := match slot with | .motive _ => motPos ++ [d - np] | _ => motPos
    match ← classReadSlots nPc np n motPos' (d + 1) (body.inst1I (← fvar d dom)) with
    | some rest => return some (slot :: rest)
    | none => return none
  | _ + 1, _, _, _ => pure none

/-- Twin of `classRead`. -/
def classRead (nP : Nat) (nPc : Name → Nat) (recs : List RecShape) : M (Option ClassRead) := do
  let some rc0 := recs.head? | return none
  let some (_, body) ← openPis nP rc0.cvR.type 0 | return none
  let some slots ← classReadSlots nPc nP (rc0.rP - nP) [] nP body | return none
  let motPos := (List.range slots.length).filter fun s =>
    match slots[s]? with | some (.motive _) => true | _ => false
  let mut recCls : List Nat := []
  for rc in recs do
    let some (_, concl) ← openPis (rc.mI + 1) rc.cvR.type 0 | return none
    let some p := headLvl (← depths) concl | return none
    let some c := classOfMotiveVar nP motPos p | return none
    recCls := recCls ++ [c]
  return some ⟨slots, recCls⟩

/-! ## The targets (twin of `RecCheck.lean`) -/

structure TargetMajor where
  ind : Name
  lvls : List Level
  ds : List Expr
  nPc : Nat
  nIdx : Nat
  ctors : List (CV × Nat)
  member : Option Nat
  nfs : List NestCtorNf := []
  pfvs : List Expr := []
  deriving Inhabited

/-- Twin of `targetAbs` (memoised by `Expr.replace`). -/
def targetAbs (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) : Expr :=
  e.replaceI fun
    | t@(.const n us) =>
      if us == lvls then
        match names.findIdx? (· == n) with
        | some t' => some (holes.getD t' t)
        | none => none
      else none
    | _ => none

/-- Twin of `targetHoles`. -/
def targetHoles (formerTys : List Expr) (base : Nat) : M (List Expr) :=
  (List.range formerTys.length).mapM fun t => fvar (base + t) (formerTys.getD t default)

/-- Twin of `targetCanonParams`. -/
def targetCanonParams (pfvs : List Expr) (e : Expr) : M Expr := replaceFVars (fun i => pfvs[i]?) e

/-- Twin of `targetParamsDefEq`. -/
def targetParamsDefEq (j : Job) (env : Kernel.Environment) (d : Nat) (absM : Expr → Expr)
    (pfvs : List Expr) : List Expr → List Expr → M Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if bvarB a == 0 && bvarB b == 0 && (← fvarB a) ≤ pfvs.length && (← fvarB b) ≤ pfvs.length then
      let a' := absM (← targetCanonParams pfvs a)
      let b' := absM (← targetCanonParams pfvs b)
      if a' == b' then targetParamsDefEq j env d absM pfvs as bs
      else
        let _ ← j.infer env d a'
        let _ ← j.infer env d b'
        if ← j.defeq env d a' b' then targetParamsDefEq j env d absM pfvs as bs else pure false
    else pure false
  | _, _ => pure false

/-- Twin of `targetClassMatch`. -/
def targetClassMatch (j : Job) (env : Kernel.Environment) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (lvls : List Level) (eds : List Expr) :
    M Bool := do
  unless lvlsEquiv us lvls do return false
  let holes ← targetHoles formerTys pfvs.length
  targetParamsDefEq j env (pfvs.length + formerTys.length)
    (targetAbs p.memberNames (p.lps.map .param) holes) pfvs ds eds

/-- Twin of `targetMajorNfs`. -/
def targetMajorNfs (j : Job) (env : Kernel.Environment) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (ctors : List (CV × Nat)) :
    List NestCtorNf → M (List NestCtorNf)
  | [] => pure []
  | e :: es => do
    let rest ← targetMajorNfs j env p formerTys pfvs us ds ctors es
    if ctors.any (·.1.name == e.ctor) then
      if ← targetClassMatch j env p formerTys pfvs us ds e.lvls e.ds then pure (e :: rest)
      else pure rest
    else pure rest

/-- Twin of `targetOutsideInst`. -/
def targetOutsideInst (env : Kernel.Environment) (I : Name) (us : List Level) (ds : List Expr) :
    M (Nat × Level) := do
  let some iv := indView? env I | throwInvalid "target rec: the recursor's major is not a stored inductive"
  let some ty := instPisWith ds (iv.cv.type.instLvlParamsI iv.cv.lps us)
    | throwInvalid "target rec: the major's type former does not bind its parameters (official: \
        ill-formed inductive type)"
  let (ibs, s) := piBinders ty
  let .sort s := s
    | throwInvalid "target rec: the major's type former is not a telescope ending in a sort \
        (official: type expected)"
  pure (ibs.length, s)

/-- Twin of `targetMajorOf`. -/
def targetMajorOf (env : Kernel.Environment) (p : BlockShape) (ctorsAs : List (List (CV × Nat)))
    (pfvs fvs : List Expr) (mty : Expr) : M TargetMajor := do
  let args := mty.getAppArgs.toList
  match mty.getAppFn with
  | .const I us =>
    match p.memberNames.findIdx? (· == I) with
    | some t =>
      let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
      let ctorsA ← unwrapOr ctorsAs[t]? (.internal "target rec: member constructors")
      unless us == p.lps.map .param && args.take p.nP == fvs.take p.nP do
        throwInvalid "target rec: the recursor's major premise is not the member at its \
          parameters and its index binders"
      pure { ind := I, lvls := us, ds := fvs.take p.nP, nPc := p.nP, nIdx := ms.nIdx,
             ctors := ctorsA, member := some t, pfvs := pfvs }
    | none =>
      if I == quotName then
        throwInvalid "target rec: the recursor's major is Quot, which is no inductive"
      let some (nPc, ctors) := nestContainer env I
        | throwInvalid "target rec: the recursor's major is not a stored inductive"
      let ds := args.take nPc
      unless ds.length == nPc do
        throwInvalid "target rec: the major's parameters mention more than the recursor's parameters"
      for x in ds do
        unless bvarB x == 0 && (← fvarB x) ≤ p.nP do
          throwInvalid "target rec: the major's parameters mention more than the recursor's \
            parameters"
      let deps ← depths
      unless ds.any (fun x => nestOcc deps p.memberNames 0 0 x) do
        throwInvalid "target rec: the recursor's major is an outside inductive at an \
          instantiation that is no auxiliary type of the block"
      let (nIdx, sI) ← targetOutsideInst env I us ds
      unless ← isEquivL sI p.resSort do
        throwInvalid "target rec: the recursor's major lives in another universe than the block (Q1)"
      pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx, ctors := ctors,
             member := none, pfvs := pfvs }
  | _ => throwInvalid "target rec: the recursor's major premise is not an inductive's application"

/-- Twin of `targetMajorPins`. -/
def targetMajorPins (j : Job) (env : Kernel.Environment) (rP : Nat) (M' : TargetMajor) : M Unit := do
  if M'.member.isNone then
    for x in M'.ds do let _ ← j.infer env rP x
    let _ ← j.infer env rP (mkAppL (.const M'.ind M'.lvls) M'.ds)

/-- Twin of `targetRecPins`. -/
def targetRecPins (p : BlockShape) (block : List SCI) : M Unit := do
  unless blockRecLpsOk p do
    throwInvalid "target rec: the recursor's level parameters are not the generated ones"
  unless blockRecNamesUnreserved p do
    throwInvalid "target rec: a recursor is named for a pinned basis constant, a literal guard's \
      slot or a certified Nat operation"
  let own := p.recs.filter fun rc => rc.tgt < p.k
  let aux := p.recs.filter fun rc => !(rc.tgt < p.k)
  unless blockRecNameSetOk { p with recs := own } do
    throwInvalid "target rec: the block's recursor names are not the generated ones (one T.rec per \
      member)"
  let n0 := (p.memberNames.head?).getD .anonymous
  let wantAux := (List.range aux.length).map fun i => n0.str s!"rec_{i + 1}"
  let gotAux := aux.map (·.cvR.name)
  unless gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) &&
      gotAux.all (wantAux.contains ·) do
    throwInvalid "target rec: the block's auxiliary recursor names are not the generated ones \
      (T.rec_1 … T.rec_n)"
  unless nodup (p.recs.map (·.cvR.name)) do
    throwInvalid "target rec: two recursors of the block share a name"
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    unless cvTs.length == p.k && rs.length == p.recs.length &&
        p.allCtors.map (·.1.name) == cs.map (·.1.name) do
      throwInvalid "target rec: the recursor record is not the generated recursor (constructor \
        grouping)"
  | none => throwInvalid "target rec: the block does not split"

/-- Twin of `targetCtorAt`. -/
def targetCtorAt (M' : TargetMajor) (c : CV) : Expr :=
  match M'.member with
  | some _ => c.type
  | none => c.type.instLvlParamsI c.lps M'.lvls

/-- Twin of `targetK53`. -/
def targetK53 (j : Job) (env : Kernel.Environment) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (majDom f : Expr) : M Bool := do
  match stripPis tele.length f with
  | none => pure false
  | some (teleW, leafW) =>
    if !(listAlpha (← teleW.mapM eraseFVarTys) (← tele.mapM eraseFVarTys)) then return false
    match leafW.getAppFn, majDom.getAppFn with
    | .const I' us', .const I _ =>
      let la := leafW.getAppArgs.toList
      let ma := majDom.getAppArgs.toList
      if I' == I && la.length == ma.length &&
          listAlpha (← (la.drop Mc.nPc).mapM eraseFVarTys) (← (ma.drop Mc.nPc).mapM eraseFVarTys) &&
          nestOcc (← depths) p.memberNames 0 0 (mkAppL (.const I' us') (la.take Mc.nPc)) then
        targetClassMatch j env p formerTys Mc.pfvs Mc.lvls Mc.ds us' (la.take Mc.nPc)
      else pure false
    | _, _ => pure false

/-- Twin of `blockLargeElimAllowed`. -/
def blockLargeElimAllowed (p : BlockShape) (nested : Bool) : Bool :=
  isNeverZero p.resSort ||
    (p.large && p.k == 1 && !nested && (p.numCtors == 0 || p.numCtors == 1))

/-- Twin of `structElimLevel`. -/
def structElimLevel (elim : Name) (large : Bool) : Level := if large then .param elim else .zero

/-- Twin of `blockNestedBit`. -/
def blockNestedBit (p : BlockShape) (kinds : List (List (List NestFieldKind))) : Bool :=
  !nestKindsFlat kinds || p.recs.any (fun rc => !(rc.tgt < p.k))

/-! ## The regeneration (twin of `GenRec.lean`) -/

inductive ClassField where
  | ordinary
  | recursive (cls : Nat) (tele : Nat)
  deriving Inhabited

structure ClassCtor where
  cv : CV
  nF : Nat
  kinds : List ClassField
  tyD : Expr
  tyN : Expr
  deriving Inhabited

structure ClassGen where
  nP : Nat
  params : List Expr
  cls : List TargetMajor
  formerTys : List Expr
  slots : List ClassSlot
  ctors : List (List ClassCtor)
  elim : Level
  pre : List Expr := []

def ClassGen.slotVar (g : ClassGen) (s : Nat) : M Expr := fvar (g.nP + s) (.sort .zero)

def ClassGen.motVar (g : ClassGen) (c : Nat) : M Expr :=
  g.slotVar ((ClassRead.motiveSlot ⟨g.slots, []⟩ c).getD 0)

def ClassGen.major (g : ClassGen) (c : Nat) (d : Nat) : M (Option (List Expr × Expr)) := do
  let ci := g.cls.getD c default
  let some ty := instPisWith ci.ds (g.formerTys.getD c default) | return none
  let some (ifs, _) ← openPis ci.nIdx ty d | return none
  return some (ifs, mkAppL (.const ci.ind ci.lvls) (ci.ds ++ ifs))

def ClassGen.motiveTy (g : ClassGen) (c d : Nat) : M (Option Expr) := do
  let some (ifs, maj) ← g.major c d | return none
  return some (← closeTelescope (← ifs.mapM fvarTypeD) d (.forallE .anonymous maj (.sort g.elim) .default))

def ClassGen.ihParts (g : ClassGen) (t : Nat) (tele : Nat) (w : Expr) (d : Nat) :
    M (Option (List Expr × List Expr)) := do
  let some (xs, leaf) ← openPis tele w d | return none
  return some (xs, leaf.getAppArgs.toList.drop (g.cls.getD t default).nPc)

def ClassGen.minorTy (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) : M (Option Expr) := do
  let ci := g.cls.getD c default
  let some (fvs, res) ← openPis x.nF x.tyD d | return none
  let some ws := targetPiDomsWith fvs x.tyN | return none
  let recs := (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none
  let mut ihs : List Expr := []
  for l in [0:recs.length] do
    let (i, t, tele) := recs.getD l default
    let e := d + x.nF + l
    let some (xs, idx) ← g.ihParts t tele (ws.getD i default) e | return none
    ihs := ihs ++ [← closeTelescope (← xs.mapM fvarTypeD) e
      (mkAppL (← g.motVar t) (idx ++ [mkAppL (fvs.getD i default) xs]))]
  let concl := mkAppL (← g.motVar c)
    (res.getAppArgs.toList.drop ci.nPc ++ [mkAppL (.const x.cv.name ci.lvls) (ci.ds ++ fvs)])
  return some (← closeTelescope ((← fvs.mapM fvarTypeD) ++ ihs) d concl)

def ClassGen.prefixBinders (g : ClassGen) : M (Option (List Expr)) := do
  let mut slotBs : List Expr := []
  for s in [0:g.slots.length] do
    let d := g.nP + s
    match g.slots.getD s default with
    | .motive _ =>
      let c := ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length
      let some t ← g.motiveTy c d | return none
      slotBs := slotBs ++ [t]
    | .minor c C _ =>
      let some x := (g.ctors.getD c []).find? (·.cv.name == C) | return none
      let some t ← g.minorTy c x d | return none
      slotBs := slotBs ++ [t]
  return some ((← g.params.mapM fvarTypeD) ++ slotBs)

/-- Twin of `classGenRecTy`. -/
def classGenRecTy (g : ClassGen) (c : Nat) : M (Option Expr) := do
  let rP := g.pre.length
  let some (ifs, maj) ← g.major c rP | return none
  let t ← fvar (rP + ifs.length) maj
  return some (← closeTelescope (g.pre ++ (← ifs.mapM fvarTypeD) ++ [maj]) 0
    (mkAppL (← g.motVar c) (ifs ++ [t])))

/-- Twin of `classGenRule`. -/
def classGenRule (g : ClassGen) (recOf : Nat → Option Name) (rlvls : List Level) (c : Nat)
    (x : ClassCtor) : M (Option Expr) := do
  let rP := g.pre.length
  let some (s, _) := (List.range g.slots.length).zip g.slots |>.find? fun (_, sl) =>
    match sl with | .minor c' C _ => c' == c && C == x.cv.name | _ => false
    | return none
  let some (fvs, _) ← openPis x.nF x.tyD rP | return none
  let some ws := targetPiDomsWith fvs x.tyN | return none
  let pvars ← (List.range rP).mapM fun i =>
    if i < g.nP then pure (g.params.getD i default) else g.slotVar (i - g.nP)
  let mut ihs : List Expr := []
  for i in [0:x.nF] do
    match x.kinds.getD i .ordinary with
    | .ordinary => pure ()
    | .recursive t tele =>
      let f := fvs.getD i default
      let some (xs, idx) ← g.ihParts t tele (ws.getD i default) (rP + x.nF) | return none
      let some r := recOf t | return none
      ihs := ihs ++ [← closeLams (← xs.mapM fvarTypeD) (rP + x.nF)
        (mkAppL (.const r rlvls) (pvars ++ idx ++ [mkAppL f xs]))]
  return some (← closeLams (g.pre ++ (← fvs.mapM fvarTypeD)) 0 (mkAppL (← g.slotVar s) (fvs ++ ihs)))

/-- Twin of `classMinorSlot`. -/
def classMinorSlot (rd : ClassRead) (c : Nat) (C : Name) : M (Nat × List (Nat × Nat)) := do
  let hits := (List.range rd.slots.length).filterMap fun s =>
    match rd.slots[s]? with
    | some (ClassSlot.minor c' C' ihs) => if c' == c && C' == C then some (s, ihs) else none
    | _ => none
  match hits with
  | [x] => pure x
  | _ => throwInvalid s!"generated recursor: the recursors' prefix does not have exactly one minor \
      premise for {C} (official: invalid recursor)"

/-- Twin of `classFieldsOf`. -/
def classFieldsOf (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) :
    Nat → List Expr → M (List ClassField)
  | _, [] => pure []
  | i, f :: fs => do
    let w ← fvarTypeD f
    let k' ← match nestOcc (← depths) p.memberNames 0 0 w, ihs.filter (·.1 == i) with
      | false, [] => pure ClassField.ordinary
      | true, [(_, t)] => pure (.recursive t (piBinders w).1.length)
      | _, _ => throwInvalid s!"generated recursor: the inductive hypotheses of {ctor}'s minor \
          premise are not its recursive fields (official: invalid recursor)"
    pure (k' :: (← classFieldsOf p ctor ihs (i + 1) fs))

def classLeafAt (M' : TargetMajor) (leaf : Expr) : Bool :=
  match leaf.getAppFn with
  | .const I _ => I == M'.ind
  | _ => false

/-- Twin of `classNodesAgree`. -/
def classNodesAgree (j : Job) (env : Kernel.Environment) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (leaf : Expr) (fvs : List Expr) (i : Nat) (ctor : Name) :
    List NestCtorNf → M Unit
  | [] => pure ()
  | e :: es => do
    let some f := ((targetPiDomsWith fvs e.ty).getD [])[i]?
      | throwInvalid s!"generated recursor: a recorded normal form of {ctor} is too short"
    unless ← targetK53 j env p formerTys Mc tele leaf f do
      throwInvalid s!"generated recursor: field {i} of {ctor} does not land at its inductive \
        hypothesis's class at every node of the positivity check (official: invalid recursor)"
    classNodesAgree j env p formerTys Mc tele leaf fvs i ctor es

/-- Twin of `classFieldsAgree`. -/
def classFieldsAgree (j : Job) (env : Kernel.Environment) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf) :
    Nat → List ClassField → M Unit
  | _, [] => pure ()
  | i, .ordinary :: ks => classFieldsAgree j env p formerTys Ms fvs ctor E (i + 1) ks
  | i, .recursive t tele :: ks => do
    let (teleB, leaf) ← unwrapOr (stripPis tele (← fvarTypeD (fvs.getD i default)))
      (.internal "generated recursor: field telescope")
    unless classLeafAt (Ms.getD t default) leaf do
      throwInvalid s!"generated recursor: field {i} of {ctor} does not end in its inductive \
        hypothesis's class (official: invalid recursor)"
    classNodesAgree j env p formerTys (Ms.getD t default) teleB leaf fvs i ctor E
    classFieldsAgree j env p formerTys Ms fvs ctor E (i + 1) ks

/-- Twin of `classCtorOf`. -/
def classCtorOf (j : Job) (env : Kernel.Environment) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (cA : CV × Nat) : M ClassCtor := do
  let E := (Ms.getD c default).nfs.filter (·.ctor == cA.1.name)
  let e0 ← unwrapOr E.head? (.internal s!"generated recursor: the constructor {cA.1.name} of a \
    class has no entry in the positivity check's table")
  let (_, ihs) ← classMinorSlot rd c cA.1.name
  let (fvs, _) ← unwrapOr (← openPis cA.2 e0.ty (p.nP + p.k))
    (.internal "generated recursor: datum telescope")
  let kinds ← classFieldsOf p cA.1.name ihs 0 fvs
  classFieldsAgree j env p formerTys Ms fvs cA.1.name E 0 kinds
  let M' := Ms.getD c default
  let tyD ← unwrapOr (instPisWith M'.ds (targetCtorAt M' cA.1))
    (.internal "generated recursor: constructor parameter telescope")
  pure ⟨cA.1, cA.2, kinds, tyD, e0.ty⟩

/-- Twin of `classesCtors`. -/
def classesCtors (j : Job) (env : Kernel.Environment) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) : M (List (List ClassCtor)) := do
  let mut out : List (List ClassCtor) := []
  for c in [0:Ms.length] do
    let M' := Ms.getD c default
    let mut xs : List ClassCtor := []
    for cA in M'.ctors do
      xs := xs ++ [← classCtorOf j env p formerTys rd Ms c cA]
    out := out ++ [xs]
  return out

/-- Twin of `classFormerTy`. -/
def classFormerTy (env : Kernel.Environment) (cvTas : List CV) (M' : TargetMajor) : M Expr :=
  match M'.member with
  | some t => pure (cvTas.getD t default).type
  | none => match indView? env M'.ind with
    | some iv => pure (iv.cv.type.instLvlParamsI iv.cv.lps M'.lvls)
    | none => throwInternal "generated recursor: a class's former vanished"

/-- Twin of `classConstOk`. -/
def classConstOk (j : Job) (env : Kernel.Environment) (cv : CV) : M Unit := do
  if (env.find? cv.name).isSome then throwInvalid s!"duplicate declaration {cv.name}"
  if reservedBasisNames.contains cv.name then throwInvalid s!"reserved basis name {cv.name}"
  unless nodup cv.lps do throwInvalid s!"duplicate universe parameters in {cv.name}"
  unless !cv.type.hasLooseBVars do
    throwInternal s!"generated recursor: loose bound variable in type of {cv.name}"
  if cv.type.hasFVar then throwInternal s!"generated recursor: free variable in type of {cv.name}"
  unless ← allLevelParamsDefined cv.lps cv.type do
    throwInvalid s!"undeclared universe parameter in type of {cv.name}"
  unless ← constsResolve env cv.type do throwInvalid s!"unknown constant in type of {cv.name}"
  let _ ← j.ensureSort env 0 (← j.infer env 0 cv.type)

/-- Twin of `classRecTyOk`. -/
def classRecTyOk (j : Job) (env : Kernel.Environment) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : CV) (c : Nat) : M CV := do
  let ci := g.cls.getD c default
  unless rc.tgt == ci.member.getD k do
    throwInvalid "generated recursor: the recursor record's member is not its class's"
  unless rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + ci.nIdx do
    throwInvalid "generated recursor: the recursor record's rule prefix or major index is not \
      the generated one"
  let gty ← unwrapOr (← classGenRecTy g c) (.internal "generated recursor: recursor type")
  let cvG := { rc.cvR with type := gty }
  classConstOk j env cvG
  unless ← j.defeq env 0 cvRi.type cvG.type do
    throwInvalid s!"generated recursor: the type of {cvG.name} is not the generated one (official: \
      invalid recursor)"
  pure cvG

/-- Twin of `classRuleCheck`/`classRuleOk`: the rule typed at the rule-less
recursors' environment `feR` (a flush entering and leaving it), its
domains resolving at the constructors' `feT`. -/
def classRuleOk (j : Job) (feT feR : Kernel.Environment) (cvR : CV) (n : Nat) (gen : Expr) :
    M Expr := do
  unless !gen.hasLooseBVars && !gen.hasFVar do
    throwInternal s!"generated recursor: a rule of {cvR.name} is not closed"
  unless ← allLevelParamsDefined cvR.lps gen do
    throwInternal s!"generated recursor: a rule of {cvR.name} names an undeclared universe parameter"
  unless ← constsResolve feR gen do throwInvalid s!"unknown constant in generated rule of {cvR.name}"
  flush
  let _ ← j.infer feR 0 gen
  flush
  let (rbs, _) ← unwrapOr (stripLams n gen) (.internal s!"generated recursor: a rule of {cvR.name} \
    is not a λ-telescope over the recursor's prefix and the constructor's fields")
  for b in rbs do
    unless ← constsResolve feT b do
      throwInvalid s!"unknown constant in the domains of a generated rule of {cvR.name}"
  pure gen

/-- Twin of `classKeyOf`. -/
def classKeyOf (nP : Nat) (params : List Expr) (k : ClassKey) : M ClassKey := do
  let k := { k with ds := ← k.ds.mapM (targetCanonParams params) }
  for x in k.ds do
    unless bvarB x == 0 && (← fvarB x) ≤ nP do
      throwInvalid "target rec: the major's parameters mention more than the recursor's parameters"
  pure k

/-- Twin of `classNPcOf`. -/
def classNPcOf (p : BlockShape) (env : Kernel.Environment) (I : Name) : Nat :=
  if p.memberNames.contains I then p.nP else (indView? env I).map (·.nparams) |>.getD 0

/-- Twin of `checkBlockClasses`. -/
def checkBlockClasses (j : Job) (env₁ : Kernel.Environment) (p : BlockShape) (params : List Expr)
    (ctorsAs : List (List (CV × Nat))) : M (ClassRead × List TargetMajor) := do
  let rd ← unwrapOr (← classRead p.nP (classNPcOf p env₁) p.recs)
    (.invalid "generated recursor: the recursor family is not of the generated shape (official: \
      invalid recursor)")
  let keys ← rd.classes.mapM (classKeyOf p.nP params)
  let mut Ms : List TargetMajor := []
  for key in keys do
    let M' ← targetMajorOf env₁ p ctorsAs params params (mkAppL (.const key.ind key.lvls) key.ds)
    targetMajorPins j env₁ p.nP M'
    Ms := Ms ++ [M']
  unless (List.range p.k).all (fun t => (Ms.filter (·.member == some t)).length == 1) do
    throwInvalid "generated recursor: the recursor family does not have exactly one class per \
      member (official: invalid recursor)"
  pure (rd, Ms)

/-- Twin of `classSeeds`. -/
def classSeeds (ctx : NestCtx) (holes : List Expr) (Ms : List TargetMajor) : M (List (NestKey × Nat)) :=
  Ms.filterMapM fun M' =>
    if M'.member.isNone then some <$> nestSeedOf ctx holes M'.ind M'.lvls M'.ds M'.nPc
    else pure none

def classRecOf (recCls : List Nat) (cvGs : List CV) (t : Nat) : Option Name :=
  ((List.range cvGs.length).find? fun r => recCls.getD r 0 == t).map fun r => (cvGs.getD r default).name

/-- The generated rules of one recursor, as Lean's records. -/
def genRules (M' : TargetMajor) (rhss : List Expr) : List RecursorRule :=
  (M'.ctors.zip rhss).map fun (c, rhs) => { ctor := c.1.name, nfields := c.2, rhs }

/-- Twin of `genRecCheck`: regenerate every recursor's type (checked
defeq to the stored one) and rules (checked at the rule-less recursors'
environment). -/
def genRecCheck (j : Job) (fe : Kernel.Environment) (p : BlockShape) (nestedBit : Bool)
    (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor)
    (cvTas : List CV) (block : List SCI) : M (List (CV × TargetMajor × List Expr)) := do
  targetRecPins p block
  let mut cvRis : List CV := []
  for rc in p.recs do
    j.checkConstantVal fe rc.cvR
    cvRis := cvRis ++ [rc.cvR]
  unless 0 < p.k do throwInvalid "generated recursor: the block declares no family"
  if p.large && !blockLargeElimAllowed p (nestedBit || Ms.any (·.member.isNone)) then
    throwInvalid "generated recursor: large eliminator on a block whose sort may be Prop (official: \
      elim_only_at_universe_zero)"
  let formerTys := cvTas.map (·.type)
  let mut Ms' : List TargetMajor := []
  for M' in Ms do
    let es ← targetMajorNfs j fe p formerTys M'.pfvs M'.lvls M'.ds M'.ctors tbl
    Ms' := Ms' ++ [{ M' with nfs := es }]
  let Ms := Ms'
  let ctors ← classesCtors j fe p formerTys rd Ms
  unless (rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum do
    throwInvalid "generated recursor: the recursors' prefix has a minor premise for no constructor \
      of a class (official: invalid recursor)"
  let formerTysC ← Ms.mapM (classFormerTy fe cvTas)
  let elim := structElimLevel p.elim p.large
  let g0 : ClassGen := ⟨p.nP, params, Ms, formerTysC, rd.slots, ctors, elim, []⟩
  let pre ← unwrapOr (← g0.prefixBinders) (.internal "generated recursor: recursor prefix")
  let g := { g0 with pre := pre }
  let mut cvGs : List CV := []
  for ((rc, cvRi), c) in (p.recs.zip cvRis).zip rd.recCls do
    cvGs := cvGs ++ [← classRecTyOk j fe g p.k rc cvRi c]
  -- the rule-less generated recursors (`classFeROvl`)
  let mut feR := fe
  for cvG in cvGs do
    feR ← j.push feR cvG.name cvG.type (some [])
  flush
  let mut out : List (CV × TargetMajor × List Expr) := []
  for (cvG, c) in cvGs.zip rd.recCls do
    let mut rhss : List Expr := []
    for x in g.ctors.getD c [] do
      let gen ← unwrapOr (← classGenRule g (classRecOf rd.recCls cvGs) (cvG.lps.map .param) c x)
        (.invalid s!"generated recursor: the rule of {x.cv.name} calls a class whose recursor the \
          stream omits (official: unknown constant)")
      rhss := rhss ++ [← classRuleOk j fe feR cvG (g.nP + g.slots.length + x.nF) gen]
    out := out ++ [(cvG, g.cls.getD c default, rhss)]
  flush
  pure out

/-! ## The stored recursors against the regenerated ones (twin of `StoredRecs.lean`) -/

/-- Twin of `recDomsAt`. -/
def recDomsAt (j : Job) (env : Kernel.Environment) (rec : Name) (sfvs gfvs : List Expr) :
    Nat → Nat → M Unit
  | _, 0 => pure ()
  | k, n + 1 => do
    let a ← unwrapOr sfvs[k]? (.internal "stored recursor: domain index")
    let b ← unwrapOr gfvs[k]? (.internal "stored recursor: domain index")
    unless ← j.defeq env k (← fvarTypeD a) (← fvarTypeD b) do
      throwInvalid s!"the type of the recursor {rec} is not the generated one: the domain of \
        binder {k} differs"
    recDomsAt j env rec sfvs gfvs (k + 1) n

/-- Twin of `recTyCheck`. -/
def recTyCheck (j : Job) (fe : Kernel.Environment) (rec : Name) (lps : List Name) (n : Nat)
    (s g : Expr) : M Unit := do
  unless !s.hasLooseBVars && !s.hasFVar && !g.hasFVar do
    throwInvalid s!"the type of the recursor {rec} is not closed"
  unless ← allLevelParamsDefined lps s do
    throwInvalid s!"undeclared universe parameter in the type of the recursor {rec}"
  unless ← constsResolve fe s do throwInvalid s!"unknown constant in the type of the recursor {rec}"
  let _ ← j.ensureSort fe 0 (← j.infer fe 0 s)
  match ← openPis n s 0, ← openPis n g 0 with
  | some (sfvs, srest), some (gfvs, grest) =>
    recDomsAt j fe rec sfvs gfvs 0 n
    unless ← j.defeq fe n srest grest do
      throwInvalid s!"the type of the recursor {rec} is not the generated one: its body after the \
        major differs"
  | none, _ =>
    throwInvalid s!"the type of the recursor {rec} is not the generated one: it has fewer than {n} \
      binders"
  | some _, none => throwInternal s!"the generated type of the recursor {rec} has fewer than {n} binders"

/-- Twin of `ruleAgree`. -/
def ruleAgree (j : Job) (fe : Kernel.Environment) (rec ctor : Name) (lps : List Name) (s g : Expr) :
    M Unit := do
  unless !s.hasLooseBVars && !s.hasFVar && !g.hasFVar do
    throwInvalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is not closed"
  unless ← allLevelParamsDefined lps s do
    throwInvalid s!"the recursor {rec}'s rule for {ctor} has an undeclared universe parameter"
  unless ← constsResolve fe s do throwInvalid s!"unknown constant in the recursor {rec}'s rule for {ctor}"
  let ts ← j.infer fe 0 s
  let tg ← j.infer fe 0 g
  unless ← j.defeq fe 0 ts tg do
    throwInvalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side whose type is not \
      the generated one's"
  unless ← j.defeq fe 0 s g do
    throwInvalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is not \
      definitionally equal to the generated one"

/-- Twin of `storedNestedOk`, the firing data `.nested lvls pins` given
as the major's container instantiation (`auxRuleFire`). -/
def storedNestedOk (ty : Expr) (mI rP : Nat) (M' : TargetMajor) : M Bool := do
  if M'.member.isSome then return true
  let pins ← M'.ds.mapM (abstractPrefix rP)
  match stripPis mI ty with
  | some (_, .forallE _ dom _ _) =>
    let headOk := match dom.getAppFn with
      | .const _ us => us == M'.lvls
      | _ => false
    let want := pins.map (·.liftLooseBVarsI 0 (mI - rP)) ++
      (List.range (mI - rP)).map fun i => Expr.bvar (mI - rP - 1 - i)
    return headOk && dom.getAppArgs.toList == want
  | _ => return false

/-- Twin of `storedRulesShape`. -/
def storedRulesShape (rec : Name) : List SRule → List (CV × Nat) → M Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      throwInvalid s!"the recursor {rec}'s rule for {r.ctor} is not the generated one's \
        (constructor {c.1.name}, {c.2} fields)"
    storedRulesShape rec rs cs
  | rs, cs => throwInvalid s!"the recursor {rec} carries {rs.length} more or fewer rules than the \
      generated one ({cs.length} unmatched)"

/-- Twin of `storedRecsCheck`: per recursor, the shape, the firing data,
the type unless it is the generated one, the rules unless they are. -/
def storedRecsCheck (j : Job) (fe : Kernel.Environment) :
    List RecShape → List (CV × TargetMajor × List Expr) → M Unit
  | rc :: rcs, (cvG, M', rhss) :: gs => do
    storedRulesShape rc.cvR.name rc.rules M'.ctors
    unless ← storedNestedOk rc.cvR.type rc.mI rc.rP M' do
      throwInternal s!"the recursor {rc.cvR.name}'s stored type does not apply its major's \
        container at the generated firing data"
    unless rc.cvR.type == cvG.type do
      recTyCheck j fe cvG.name cvG.lps (rc.mI + 1) rc.cvR.type cvG.type
    for (r, g) in rc.rules.zip rhss do
      unless r.rhs == g do ruleAgree j fe cvG.name r.ctor cvG.lps r.rhs g
    storedRecsCheck j fe rcs gs
  | [], [] => pure ()
  | _, _ => throwInternal "stored recursors: the generated family is not the records'"

end IC

end Lean.Kernel.InLean
