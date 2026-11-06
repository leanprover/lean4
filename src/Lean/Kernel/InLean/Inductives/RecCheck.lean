/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.ClassRead

/-!
# InLean's inductive check: the recursors' targets

Twin of `ConLeche/Kernel/Inductives/RecCheck.lean` (each class's major, the
recursor records' pins, the generated rules and K flag) and of
`BlockRec.lean`'s `blockLargeElimAllowed`.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- Twin of `targetAbs`: a member at the block's levels to its hole. -/
def targetAbs (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) : Expr :=
  EO.replace (fun
    | x@(.const n us) =>
      if us == lvls then
        match names.findIdx? (· == n) with
        | some t => some (holes.getD t x)
        | none => some x
      else some x
    | _ => none) e

/-- Twin of `targetHoles`. -/
def targetHoles (formerTys : List Expr) (base : Nat) : CheckCM (List Expr) :=
  (List.range formerTys.length).mapM fun t => mkFVarM (base + t) (formerTys.getD t default)

/-- Twin of `TargetMajor`. -/
structure TargetMajor where
  ind : Name
  lvls : List Level
  ds : List Expr
  nPc : Nat
  nIdx : Nat
  ctors : List (ConstantVal × Nat)
  member : Option Nat
  nfs : List NestCtorNf := []
  pfvs : List Expr := []
  deriving Inhabited

/-- Twin of `classFeR`. -/
def classFeR (p : BlockShape) (Ms : List TargetMajor) (cvGs : List ConstantVal)
    (recCls : List Nat) (fe : FEnv) : FEnv :=
  consBlockRecsBareF p 0 ((cvGs.zip recCls).map fun (cv, c) => (cv, (Ms.getD c default).nIdx)) fe

/-- Twin of `ShadowOps CheckCM`. -/
structure ShadowOps where
  opsAt : FEnv → CheckerOps
  opsRuleR : FEnv → CheckerOps
  flush : CheckCM Unit
  walkers : StructWalkers
  ruleEnv : BlockShape → List TargetMajor → List ConstantVal → List Nat → FEnv → FEnv

/-- Twin of `targetCanonParams`. -/
def targetCanonParams (pfvs : List Expr) (e : Expr) : Expr :=
  replaceFVars (fun i => pfvs[i]?) e

/-- Twin of `targetParamsDefEq`. -/
def targetParamsDefEq (ops : CheckerOps) (env : FEnv) (d : Nat) (absM : Expr → Expr)
    (pfvs : List Expr) : List Expr → List Expr → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if !a.hasLooseBVars && !b.hasLooseBVars && fvarB a ≤ pfvs.length && fvarB b ≤ pfvs.length then
      let a' := absM (targetCanonParams pfvs a)
      let b' := absM (targetCanonParams pfvs b)
      if a' == b' then targetParamsDefEq ops env d absM pfvs as bs
      else
        let _ ← ops.inferType env d a'
        let _ ← ops.inferType env d b'
        if ← ops.isDefEq env d a' b' then targetParamsDefEq ops env d absM pfvs as bs
        else pure false
    else pure false
  | _, _ => pure false

/-- Twin of `Level.isEquivList`. -/
def isEquivList : List Level → List Level → Option Bool
  | [], [] => some true
  | l :: ls, r :: rs =>
    match Lvl.isEquiv l r with
    | some true => isEquivList ls rs
    | o => o
  | _, _ => some false

/-- Twin of `targetClassMatch`. -/
def targetClassMatch (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (lvls : List Level) (eds : List Expr) :
    CheckCM Bool := do
  unless isEquivList us lvls == some true do return false
  let holes ← targetHoles formerTys pfvs.length
  targetParamsDefEq ops env (pfvs.length + formerTys.length)
    (targetAbs p.memberNames (p.lps.map .param) holes) pfvs ds eds

/-- Twin of `targetMajorNfs`. -/
def targetMajorNfs (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (ctors : List (ConstantVal × Nat)) :
    List NestCtorNf → CheckCM (List NestCtorNf)
  | [] => pure []
  | e :: es => do
    let rest ← targetMajorNfs ops env p formerTys pfvs us ds ctors es
    if ctors.any (·.1.name == e.ctor) then
      if ← targetClassMatch ops env p formerTys pfvs us ds e.lvls e.ds then pure (e :: rest)
      else pure rest
    else pure rest

/-- Twin of `targetCtorsOf`. -/
def targetCtorsOf (fe : FEnv) (I : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  nestContainer ⟨[], [], 0, [], [], .zero, fe, []⟩ I

/-- Twin of `targetOutsideInst`. -/
def targetOutsideInst (ops : CheckerOps) (fe : FEnv) (I : Name) (us : List Level) (ds : List Expr) :
    CheckCM (Nat × Level) := do
  let some (cvI, capsI) := fe.indView? I
    | throw (.invalid "target rec: the recursor's major is not a stored inductive")
  let tyI ← familyTelescope ops fe cvI capsI
  let some ty := instPisWith ds (tyI.instLvlParamsI cvI.levelParams us)
    | throw (.invalid "target rec: the major's type former does not bind its parameters \
        (official: ill-formed inductive type)")
  let (ibs, s) := piBinders ty
  let .sort s := s
    | throw (.invalid "target rec: the major's type former is not a telescope ending in a \
        sort (official: type expected)")
  pure (ibs.length, s)

/-- Twin of `targetMajorOf`. -/
def targetMajorOf (ops : CheckerOps) (fe : FEnv) (p : BlockShape) (pfvs fvs : List Expr)
    (mty : Expr) : CheckCM TargetMajor := do
  let args := appArgs mty
  match mty.getAppFn with
  | .const I us =>
    match p.memberNames.findIdx? (· == I) with
    | some t => do
      let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
      unless us == p.lps.map .param && args.take p.nP == fvs.take p.nP do
        throw (.invalid "target rec: the recursor's major premise is not the member at its \
          parameters and its index binders")
      pure { ind := I, lvls := us, ds := fvs.take p.nP, nPc := p.nP, nIdx := ms.nIdx,
             ctors := ms.ctors, member := some t, pfvs := pfvs }
    | none => do
      if I == quotName then
        throw (.invalid "target rec: the recursor's major is Quot, which is no inductive")
      let some (nPc, ctors) := targetCtorsOf fe I
        | throw (.invalid "target rec: the recursor's major is not a stored inductive")
      let ds := args.take nPc
      unless ds.length == nPc && ds.all (fun x => !x.hasLooseBVars && fvarB x ≤ p.nP) do
        throw (.invalid "target rec: the major's parameters mention more than the \
          recursor's parameters")
      unless ds.any (fun x => nestOcc p.memberNames 0 0 x) do
        throw (.invalid "target rec: the recursor's major is an outside inductive at an \
          instantiation that is no auxiliary type of the block (official generates no such \
          auxiliary recursor: `elim_nested_inductive`, `is_nested`)")
      let (nIdx, sI) ← targetOutsideInst ops fe I us ds
      unless ← liftFueled "level comparison" (Lvl.isEquiv sI p.resSort) do
        throw (.invalid "target rec: the recursor's major lives in another universe than \
          the block (Q1)")
      pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx, ctors := ctors,
             member := none, pfvs := pfvs }
  | _ => throw (.invalid "target rec: the recursor's major premise is not an inductive's \
      application")

/-- Twin of `targetPinTys`. -/
def targetPinTys (ops : CheckerOps) (env : FEnv) (d : Nat) : List Expr → CheckCM Unit
  | [] => pure ()
  | x :: xs => do
    let _ ← ops.inferType env d x
    targetPinTys ops env d xs

/-- Twin of `targetMajorPins`. -/
def targetMajorPins (ops : CheckerOps) (fe : FEnv) (rP : Nat) (M : TargetMajor) : CheckCM Unit :=
  if M.member.isNone then do
    targetPinTys ops fe rP M.ds
    familyKeyCheck ops fe rP M.ind M.lvls M.ds
  else pure ()

/-- Twin of `targetRecPins`. -/
def targetRecPins (p : BlockShape) (block : List ConstantInfo) : CheckCM Unit := do
  unless blockRecLpsOk p do
    throw (.invalid "target rec: the recursor's level parameters are not the generated ones")
  unless blockRecNamesUnreserved p do
    throw (.invalid "target rec: a recursor is named for a pinned basis constant, a literal \
      guard's slot or a certified Nat operation")
  let own := p.recs.filter fun rc => rc.tgt < p.k
  let aux := p.recs.filter fun rc => !(rc.tgt < p.k)
  unless blockRecNameSetOk { p with recs := own } do
    throw (.invalid "target rec: the block's recursor names are not the generated ones \
      (one T.rec per member)")
  let n0 := (p.memberNames.head?).getD .anonymous
  let wantAux := (List.range aux.length).map fun i => n0.str s!"rec_{i + 1}"
  let gotAux := aux.map (·.cvR.name)
  unless gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) &&
      gotAux.all (wantAux.contains ·) do
    throw (.invalid "target rec: the block's auxiliary recursor names are not the generated \
      ones (T.rec_1 … T.rec_n)")
  unless namesNodup (p.recs.map (·.cvR.name)) do
    throw (.invalid "target rec: two recursors of the block share a name")
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    unless cvTs.length == p.k && rs.length == p.recs.length &&
        p.allCtors.map (·.1.name) == cs.map (·.1.name) do
      throw (.invalid "target rec: the recursor record is not the generated recursor \
        (constructor grouping)")
  | none => throw (.invalid "target rec: the block does not split")

/-- Twin of `targetCtorAt`. -/
def targetCtorAt (M : TargetMajor) (c : ConstantVal) : Expr :=
  match M.member with
  | some _ => c.type
  | none => c.type.instLvlParamsI c.levelParams M.lvls

/-- Twin of `targetK53`. -/
def targetK53 (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (majDom f : Expr) : CheckCM Bool := do
  match stripPis tele.length f with
  | none => pure false
  | some (teleW, leafW) =>
    if (← teleW.mapM eraseFVarTys) != (← tele.mapM eraseFVarTys) then pure false
    else
      match leafW.getAppFn, majDom.getAppFn with
      | .const I' us', .const I _ =>
        if I' == I && leafW.getAppNumArgs == majDom.getAppNumArgs &&
            (← ((appArgs leafW).drop Mc.nPc).mapM eraseFVarTys)
              == (← ((appArgs majDom).drop Mc.nPc).mapM eraseFVarTys) &&
            nestOcc p.memberNames 0 0 (mkAppL (.const I' us') ((appArgs leafW).take Mc.nPc)) then
          targetClassMatch ops env p formerTys Mc.pfvs Mc.lvls Mc.ds us'
            ((appArgs leafW).take Mc.nPc)
        else pure false
      | _, _ => pure false

/-- Twin of `auxRuleFire`. -/
def auxRuleFire (M : TargetMajor) (rP : Nat) : RecRuleFire :=
  .nested M.lvls (M.ds.map (abstractPrefix rP 0))

/-- Twin of `sumRules`. -/
def sumRules : List (ConstantVal × Nat) → List Expr → List RecursorRule
  | c :: cs, rhs :: rhss => { ctor := c.1.name, nfields := c.2, rhs } :: sumRules cs rhss
  | _, _ => []

/-- Twin of `generatedRules`: the firing mode is not part of a Lean rule; it
is read off the recursor's type at use (`recFireAt`), which for an outside
major is `auxRuleFire`'s (`streamNestedOk`). -/
def generatedRules (M : TargetMajor) (rhss : List Expr) : List RecursorRule :=
  sumRules M.ctors rhss

/-- Twin of `recKExpected`. -/
def recKExpected (p : BlockShape) (M : TargetMajor) : Bool :=
  match M.member, M.ctors with
  | some _, [c] => p.k == 1 && p.isProp && c.2 == 0
  | _, _ => false

/-- Twin of `blockNestedBit`. -/
def blockNestedBit (p : BlockShape) (kinds : List (List (List NestFieldKind))) : Bool :=
  !nestKindsFlat kinds || p.recs.any (fun rc => !(rc.tgt < p.k))

/-- Twin of `blockRecInfosTF`. -/
def blockRecInfosTF (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) →
    List ConstantInfo
  | _, [] => []
  | m, (cv, M, rhss) :: rest =>
    recEntry p cv (p.majorIdxAt m) (p.rulePrefixAt m) (recKExpected p M) (generatedRules M rhss)
      :: blockRecInfosTF p (m + 1) rest

/-- Twin of `Level.isNeverZero`. -/
def isNeverZero : Level → Bool
  | .zero => false
  | .succ _ => true
  | .max a b => isNeverZero a || isNeverZero b
  | .imax _ b => isNeverZero b
  | .param _ | .mvar _ => false

/-- Twin of `blockLargeElimAllowed` (`BlockRec.lean`). -/
def blockLargeElimAllowed (p : BlockShape) (nested : Bool) : Bool :=
  isNeverZero p.resSort ||
    (p.large && p.k == 1 && !nested && (p.numCtors == 0 || p.numCtors == 1))

end Lean.Kernel.InLean
