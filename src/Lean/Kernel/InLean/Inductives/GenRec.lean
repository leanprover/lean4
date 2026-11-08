/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.RecCheck

/-!
# InLean's inductive check: the generated recursors

Twin of `ConLeche.Kernel.Inductives.GenRec`: every recursor of the block
regenerated from its classes (its type and its rules) and checked.  What
con-leche writes in `Option` (a shape that may not be there) is in
`OptionT CheckCM` here, because its variables are interned.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- An `Option` in `OptionT CheckCM`. -/
@[inline] def liftOpt (o : Option α) : OptionT CheckCM α := OptionT.mk (pure o)

/-- `openPisAtFvars` in `OptionT CheckCM`. -/
@[inline] def openPisO (n : Nat) (e : Expr) (i : Nat) : OptionT CheckCM (List Expr × Expr) :=
  OptionT.mk (openPisAtFvars n e i)

/-- Twin of `ClassField`. -/
inductive ClassField where
  | ordinary
  | recursive (cls : Nat) (tele : Nat)
  deriving BEq, Inhabited

/-- Twin of `ClassCtor`. -/
structure ClassCtor where
  cv : ConstantVal
  nF : Nat
  kinds : List ClassField
  tyD : Expr
  tyN : Expr
  deriving Inhabited

/-- Twin of `ClassGen`. -/
structure ClassGen where
  nP : Nat
  params : List Expr
  cls : List TargetMajor
  formerTys : List Expr
  slots : List ClassSlot
  ctors : List (List ClassCtor)
  elim : Level
  pre : List Expr := []

/-- Twin of `ClassGen.binder`. -/
def ClassGen.binder (_g : ClassGen) (x : Expr) : CheckCM Expr := fvarTypeD x

/-- Twin of `ClassGen.slotVar`. -/
def ClassGen.slotVar (g : ClassGen) (s : Nat) : CheckCM Expr := mkFVarM (g.nP + s) (.sort .zero)

/-- Twin of `ClassGen.motVar`. -/
def ClassGen.motVar (g : ClassGen) (c : Nat) : CheckCM Expr :=
  g.slotVar ((ClassRead.motiveSlot ⟨g.slots, []⟩ c).getD 0)

/-- Twin of `ClassGen.major`. -/
def ClassGen.major (g : ClassGen) (c : Nat) (d : Nat) : OptionT CheckCM (List Expr × Expr) := do
  let ci := g.cls.getD c default
  let ty ← liftOpt (instPisWith ci.ds (g.formerTys.getD c default))
  let (ifs, _) ← openPisO ci.nIdx ty d
  pure (ifs, mkAppL (.const ci.ind ci.lvls) (ci.ds ++ ifs))

/-- Twin of `ClassGen.motiveTy`. -/
def ClassGen.motiveTy (g : ClassGen) (c d : Nat) : OptionT CheckCM Expr := do
  let (ifs, maj) ← g.major c d
  pure (closeTelescope (← ifs.mapM fun x => liftM (fvarTypeD x)) d (.forallE .anonymous maj (.sort g.elim) .default))

/-- Twin of `ClassGen.ihParts`. -/
def ClassGen.ihParts (g : ClassGen) (t : Nat) (tele : Nat) (w : Expr) (d : Nat) :
    OptionT CheckCM (List Expr × List Expr) := do
  let (xs, leaf) ← openPisO tele w d
  pure (xs, (appArgs leaf).drop (g.cls.getD t default).nPc)

/-- Twin of `ClassGen.minorTy`. -/
def ClassGen.minorTy (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) : OptionT CheckCM Expr := do
  let ci := g.cls.getD c default
  let (fvs, res) ← openPisO x.nF x.tyD d
  let ws ← liftOpt (targetPiDomsWith fvs x.tyN)
  let recs := (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none
  let ihs ← (List.range recs.length).mapM fun l => do
    let (i, t, tele) := recs.getD l default
    let e := d + x.nF + l
    let (xs, idx) ← g.ihParts t tele (ws.getD i default) e
    pure (closeTelescope (← xs.mapM fun x => liftM (g.binder x)) e
      (mkAppL (← g.motVar t) (idx ++ [mkAppL (fvs.getD i default) xs])))
  let concl := mkAppL (← g.motVar c)
    ((appArgs res).drop ci.nPc ++ [mkAppL (.const x.cv.name ci.lvls) (ci.ds ++ fvs)])
  pure (closeTelescope ((← fvs.mapM fun x => liftM (g.binder x)) ++ ihs) d concl)

/-- Twin of `ClassGen.prefixBinders`. -/
def ClassGen.prefixBinders (g : ClassGen) : OptionT CheckCM (List Expr) := do
  let slotBs ← (List.range g.slots.length).mapM fun s => do
    let d := g.nP + s
    match g.slots.getD s default with
    | .motive _ =>
      let c := ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length
      g.motiveTy c d
    | .minor c C _ =>
      let x ← liftOpt ((g.ctors.getD c []).find? (·.cv.name == C))
      g.minorTy c x d
  pure ((← g.params.mapM fun x => liftM (g.binder x)) ++ slotBs)

/-- Twin of `classGenRecTy`. -/
def classGenRecTy (g : ClassGen) (c : Nat) : OptionT CheckCM Expr := do
  let pre := g.pre
  let rP := pre.length
  let (ifs, maj) ← g.major c rP
  let t ← mkFVarM (rP + ifs.length) maj
  pure (closeTelescope (pre ++ (← ifs.mapM fun x => liftM (g.binder x)) ++ [maj]) 0
    (mkAppL (← g.motVar c) (ifs ++ [t])))

/-- Twin of `classGenRule`. -/
def classGenRule (g : ClassGen) (recOf : Nat → Option Name) (rlvls : List Level) (c : Nat)
    (x : ClassCtor) : OptionT CheckCM Expr := do
  let pre := g.pre
  let rP := pre.length
  let (s, _) ← liftOpt ((List.range g.slots.length).zip g.slots |>.find? fun (_, sl) =>
    match sl with | .minor c' C _ => c' == c && C == x.cv.name | _ => false)
  let (fvs, _) ← openPisO x.nF x.tyD rP
  let ws ← liftOpt (targetPiDomsWith fvs x.tyN)
  let pvars ← (List.range rP).mapM fun i =>
    if i < g.nP then pure (g.params.getD i default) else g.slotVar (i - g.nP)
  let ihs ← (List.range x.nF).filterMapM fun i => do
    match x.kinds.getD i .ordinary with
    | .ordinary => pure none
    | .recursive t tele =>
      let f := fvs.getD i default
      let (xs, idx) ← g.ihParts t tele (ws.getD i default) (rP + x.nF)
      let r ← liftOpt (recOf t)
      pure (some (closeLams (← xs.mapM fun x => liftM (g.binder x)) (rP + x.nF)
        (mkAppL (.const r rlvls) (pvars ++ idx ++ [mkAppL f xs]))))
  pure (closeLams (pre ++ (← fvs.mapM fun x => liftM (g.binder x))) 0 (mkAppL (← g.slotVar s) (fvs ++ ihs)))

/-- Twin of `ClassSlot.isMinor`. -/
def ClassSlot.isMinor : ClassSlot → Bool
  | .minor .. => true
  | .motive _ => false

/-- Twin of `classMinorSlot`. -/
def classMinorSlot (rd : ClassRead) (c : Nat) (C : Name) : CheckCM (Nat × List (Nat × Nat)) := do
  let hits := (List.range rd.slots.length).filterMap fun s =>
    match (rd.slots[s]? : Option ClassSlot) with
    | some (.minor c' C' ihs) => if c' == c && C' == C then some (s, ihs) else none
    | _ => none
  match hits with
  | [x] => pure x
  | _ => throw (.invalid s!"generated recursor: the recursors' prefix does not have exactly one \
      minor premise for {C} (official: invalid recursor)")

/-- Twin of `classFieldsOf`. -/
def classFieldsOf (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) :
    Nat → List Expr → CheckCM (List ClassField)
  | _, [] => pure []
  | i, f :: fs => do
    let w ← fvarTypeD f
    let k' ← match nestOcc p.memberNames 0 0 w, ihs.filter (·.1 == i) with
      | false, [] => pure ClassField.ordinary
      | true, [(_, t)] => pure (.recursive t (piBinders w).1.length)
      | _, _ =>
        throw (.invalid s!"generated recursor: the inductive hypotheses of {ctor}'s minor \
          premise are not its recursive fields (official: invalid recursor)")
    let ks' ← classFieldsOf p ctor ihs (i + 1) fs
    pure (k' :: ks')

/-- Twin of `classNodesAgree`. -/
def classNodesAgree (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (leaf : Expr) (fvs : List Expr) (i : Nat) (ctor : Name) :
    List NestCtorNf → CheckCM Unit
  | [] => pure ()
  | e :: es => do
    let some f := ((targetPiDomsWith fvs e.ty).getD [])[i]?
      | throw (.invalid s!"generated recursor: a recorded normal form of {ctor} is too short")
    unless ← targetK53 ops env p formerTys Mc tele leaf f do
      throw (.invalid s!"generated recursor: field {i} of {ctor} does not land at its inductive \
        hypothesis's class at every node of the positivity check (official: invalid recursor)")
    classNodesAgree ops env p formerTys Mc tele leaf fvs i ctor es

/-- Twin of `classLeafAt`. -/
def classLeafAt (M : TargetMajor) (leaf : Expr) : Bool :=
  match leaf.getAppFnT with
  | .const I _ => I == M.ind
  | _ => false

/-- Twin of `classFieldsAgree`. -/
def classFieldsAgree (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf) :
    Nat → List ClassField → CheckCM Unit
  | _, [] => pure ()
  | i, .ordinary :: ks => classFieldsAgree ops env p formerTys Ms fvs ctor E (i + 1) ks
  | i, .recursive t tele :: ks => do
    let (teleB, leaf) ← unwrapOr (stripPis tele (← fvarTypeD (fvs.getD i default)))
      (.internal "generated recursor: field telescope")
    unless classLeafAt (Ms.getD t default) leaf do
      throw (.invalid s!"generated recursor: field {i} of {ctor} does not end in its inductive \
        hypothesis's class (official: invalid recursor)")
    classNodesAgree ops env p formerTys (Ms.getD t default) teleB leaf fvs i ctor E
    classFieldsAgree ops env p formerTys Ms fvs ctor E (i + 1) ks

/-- Twin of `classCtorOf`. -/
def classCtorOf (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (ctor : ConstantVal × Nat) :
    CheckCM ClassCtor := do
  let E := (Ms.getD c default).nfs.filter (·.ctor == ctor.1.name)
  let e0 ← unwrapOr E.head? (.internal s!"generated recursor: the constructor {ctor.1.name} of a \
    class has no entry in the positivity check's table")
  let (_, ihs) ← classMinorSlot rd c ctor.1.name
  let (fvs, _) ← unwrapOr (← openPisAtFvars ctor.2 e0.ty (p.nP + p.k))
    (.internal "generated recursor: datum telescope")
  let kinds ← classFieldsOf p ctor.1.name ihs 0 fvs
  classFieldsAgree ops env p formerTys Ms fvs ctor.1.name E 0 kinds
  let M := Ms.getD c default
  let tyD ← unwrapOr (instPisWith M.ds (← targetCtorAt M ctor.1))
    (.internal "generated recursor: constructor parameter telescope")
  pure ⟨ctor.1, ctor.2, kinds, tyD, e0.ty⟩

/-- Twin of `classCtorsOf`. -/
def classCtorsOf (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) :
    List (ConstantVal × Nat) → CheckCM (List ClassCtor)
  | [] => pure []
  | ctor :: cs => do
    let x ← classCtorOf ops env p formerTys rd Ms c ctor
    let xs ← classCtorsOf ops env p formerTys rd Ms c cs
    pure (x :: xs)

/-- Twin of `classesCtors`. -/
def classesCtors (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) : Nat → List TargetMajor → CheckCM (List (List ClassCtor))
  | _, [] => pure []
  | c, M :: rest => do
    let xs ← classCtorsOf ops env p formerTys rd Ms c M.ctors
    let xss ← classesCtors ops env p formerTys rd Ms (c + 1) rest
    pure (xs :: xss)

/-- Twin of `classMajors`. -/
def classMajors (ops : CheckerOps) (fe : FEnv) (p : BlockShape) (pfvs : List Expr) :
    List ClassKey → CheckCM (List TargetMajor)
  | [] => pure []
  | key :: keys => do
    let M ← targetMajorOf ops fe p pfvs pfvs (mkAppL (.const key.ind key.lvls) key.ds)
    targetMajorPins ops fe p.nP M
    let Ms ← classMajors ops fe p pfvs keys
    pure (M :: Ms)

/-- Twin of `classesNfs`. -/
def classesNfs (ops : CheckerOps) (env : FEnv) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) : List TargetMajor → CheckCM (List TargetMajor)
  | [] => pure []
  | M :: Ms => do
    let es ← targetMajorNfs ops env p formerTys M.pfvs M.lvls M.ds M.ctors tbl
    let rest ← classesNfs ops env p formerTys tbl Ms
    pure ({ M with nfs := es } :: rest)

/-- Twin of `classFormerTy`. -/
def classFormerTy (ops : CheckerOps) (fe : FEnv) (formers : List ConstantVal) (M : TargetMajor) :
    CheckCM Expr :=
  match M.member with
  | some t => pure (formers.getD t default).type
  | none => match fe.indView? M.ind with
    | some (cv, caps) => do
      let ty ← familyTelescope ops fe cv caps
      instLevelParamsM cv.levelParams M.lvls ty
    | none => throw (.internal "generated recursor: a class's former vanished")

/-- Twin of `classConstOk`; the name's freshness read off the environment
itself (`checkConstantValF`).  The generated type was closed by depth
(`EO.abstractDepthsFrom`), which may write `EO.rangePoison`: a type
`EO.inRange` refuses is an error, as in `reducedFormer`. -/
def classConstOk (ops : CheckerOps) (fe : FEnv) (cv : ConstantVal) : CheckCM Unit := do
  if (fe.env.find? cv.name).isSome then throw (.invalid s!"duplicate declaration {cv.name}")
  unless litShapeOk cv.name cv.levelParams cv.type do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless namesNodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  if cv.type.hasLooseBVars then
    throw (.internal s!"generated recursor: loose bound variable in type of {cv.name}")
  if cv.type.hasFVar then
    throw (.internal s!"generated recursor: free variable in type of {cv.name}")
  unless EO.inRange cv.type do throw (.internal "too many bound variables")
  unless ← allLevelParamsDefined cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless ← constsResolveF fe cv.type do
    throw (unresolvedConstsErrorL true s!"type of {cv.name}" cv.type)
  let stype ← ops.inferType fe 0 cv.type
  let _u ← ops.ensureSort fe 0 stype

/-- Twin of `classRecTyCheck`. -/
def classRecTyCheck (ops : CheckerOps) (fe : FEnv) (cvRi cvG : ConstantVal) : CheckCM Unit := do
  classConstOk ops fe cvG
  unless ← ops.isDefEq fe 0 cvRi.type cvG.type do
    throw (.invalid s!"generated recursor: the type of {cvG.name} is not the generated one \
      (official: invalid recursor)")

/-- Twin of `classRecTyOk`. -/
def classRecTyOk (ops : CheckerOps) (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) : CheckCM ConstantVal := do
  let ci := g.cls.getD c default
  unless rc.tgt == ci.member.getD k do
    throw (.invalid "generated recursor: the recursor record's member is not its class's")
  unless rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + ci.nIdx do
    throw (.invalid "generated recursor: the recursor record's rule prefix or major index is \
      not the generated one")
  let gty ← unwrapOr (← (classGenRecTy g c).run) (.internal "generated recursor: recursor type")
  let cvG := { rc.cvR with type := gty }
  classRecTyCheck ops fe cvRi cvG
  pure cvG

/-- Twin of `classRecTysOk`. -/
def classRecTysOk (ops : CheckerOps) (fe : FEnv) (g : ClassGen) (k : Nat) :
    List RecShape → List ConstantVal → List Nat → CheckCM (List ConstantVal)
  | rc :: rcs, cvRi :: cvs, c :: cs => do
    let x ← classRecTyOk ops fe g k rc cvRi c
    let xs ← classRecTysOk ops fe g k rcs cvs cs
    pure (x :: xs)
  | [], _, _ => pure []
  | _, _, _ => throw (.internal "generated recursor: recursor list")

/-- Twin of `classRuleCheck`; a rule `EO.inRange` refuses is an error, as in
`classConstOk`. -/
def classRuleCheck (ops : CheckerOps) (w : StructWalkers) (feT feR : FEnv) (cvR : ConstantVal)
    (n : Nat) (gen : Expr) : CheckCM Unit := do
  unless !gen.hasLooseBVars && !gen.hasFVar do
    throw (.internal s!"generated recursor: a rule of {cvR.name} is not closed")
  unless EO.inRange gen do throw (.internal "too many bound variables")
  unless ← allLevelParamsDefined cvR.levelParams gen do
    throw (.internal s!"generated recursor: a rule of {cvR.name} names an undeclared universe \
      parameter")
  unless ← w.resolve feR gen do
    throw (unresolvedConstsErrorL true s!"generated rule of {cvR.name}" gen)
  let _ ← ops.inferType feR 0 gen
  let (rbs, _) ← unwrapOr (stripLams n gen)
    (.internal s!"generated recursor: a rule of {cvR.name} is not a λ-telescope over the \
      recursor's prefix and the constructor's fields")
  unless ← rbs.allM (w.resolve feT) do
    throw (unresolvedConstsErrorL true s!"the domains of a generated rule of {cvR.name}" gen)

/-- Twin of `classRuleOk`. -/
def classRuleOk (ops : CheckerOps) (w : StructWalkers) (feT feR : FEnv) (cvR : ConstantVal)
    (n : Nat) (gen : Expr) : CheckCM Expr := do
  classRuleCheck ops w feT feR cvR n gen
  pure gen

/-- Twin of `classRulesOk`. -/
def classRulesOk (ops : CheckerOps) (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) (cvR : ConstantVal) (c : Nat) : List ClassCtor → CheckCM (List Expr)
  | [] => pure []
  | x :: xs => do
    let gen ← unwrapOr (← (classGenRule g recOf (cvR.levelParams.map .param) c x).run)
      (.invalid s!"generated recursor: the rule of {x.cv.name} calls a class whose recursor the \
        stream omits (official: unknown constant)")
    let r ← classRuleOk ops w feT feR cvR (g.nP + g.slots.length + x.nF) gen
    let rs ← classRulesOk ops w feT feR g recOf cvR c xs
    pure (r :: rs)

/-- Twin of `classRecsRulesOk`. -/
def classRecsRulesOk (ops : CheckerOps) (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) :
    List ConstantVal → List Nat → CheckCM (List (ConstantVal × TargetMajor × List Expr))
  | cvG :: cvs, c :: cs => do
    let rhss ← classRulesOk ops w feT feR g recOf cvG c (g.ctors.getD c [])
    let xs ← classRecsRulesOk ops w feT feR g recOf cvs cs
    pure ((cvG, g.cls.getD c default, rhss) :: xs)
  | _, _ => pure []

/-- Twin of `classStreamRecs`. -/
def classStreamRecs (ops : CheckerOps) (fe : FEnv) : List RecShape → CheckCM (List ConstantVal)
  | [] => pure []
  | rc :: rcs => do
    checkConstantValF ops fe rc.cvR
    let cvs ← classStreamRecs ops fe rcs
    pure (rc.cvR :: cvs)

/-- Twin of `classKeyCanon`. -/
def classKeyCanon (params : List Expr) (k : ClassKey) : ClassKey :=
  { k with ds := k.ds.map (targetCanonParams params) }

/-- Twin of `classNPcOf`. -/
def classNPcOf (p : BlockShape) (fe : FEnv) (I : Name) : Nat :=
  if p.memberNames.contains I then p.nP else
    match fe.indView? I with
    | some (_, caps) => caps.nparams
    | none => 0

/-- Twin of `classSeeds`. -/
def classSeeds (ctx : NestCtx) (holes : List Expr) (Ms : List TargetMajor) :
    CheckCM (List (NestKey × Nat)) :=
  Ms.filterMapM fun M =>
    if M.member.isNone then some <$> nestSeedOf ctx holes M.ind M.lvls M.ds M.nPc else pure none

/-- Twin of `classKeyOf`. -/
def classKeyOf (nP : Nat) (params : List Expr) (k : ClassKey) : CheckCM ClassKey := do
  let k := classKeyCanon params k
  unless k.ds.all (fun x => !x.hasLooseBVars && fvarB x ≤ nP) do
    throw (.invalid "target rec: the major's parameters mention more than the \
      recursor's parameters")
  pure k

/-- Twin of `checkBlockClasses`. -/
def checkBlockClasses (ops : CheckerOps) (fe₁ : FEnv) (p : BlockShape) (params : List Expr) :
    CheckCM (ClassRead × List TargetMajor) := do
  let rd ← unwrapOr (← classRead p.nP (classNPcOf p fe₁) p.recs)
    (.invalid "generated recursor: the recursor family is not of the generated shape \
      (official: invalid recursor)")
  let keys ← rd.classes.mapM (classKeyOf p.nP params)
  let Ms ← classMajors ops fe₁ p params keys
  unless (List.range p.k).all (fun t => (Ms.filter (·.member == some t)).length == 1) do
    throw (.invalid "generated recursor: the recursor family does not have exactly one class \
      per member (official: invalid recursor)")
  pure (rd, Ms)

/-- Twin of `classRecOf`. -/
def classRecOf (recCls : List Nat) (cvGs : List ConstantVal) (t : Nat) : Option Name :=
  ((List.range cvGs.length).find? fun r => recCls.getD r 0 == t).map fun r =>
    (cvGs.getD r default).name

/-- Twin of `genRecCheck`. -/
def genRecCheck (so : ShadowOps) (fe : FEnv) (p : BlockShape) (nestedBit : Bool)
    (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor)
    (block : List ConstantInfo) : CheckCM (List (ConstantVal × TargetMajor × List Expr)) := do
  targetRecPins p block
  let ops := so.opsAt fe
  let cvRis ← classStreamRecs ops fe p.recs
  unless 0 < p.k do throw (.invalid "generated recursor: the block declares no family")
  if p.large && !blockLargeElimAllowed p (nestedBit || Ms.any (·.member.isNone)) then
    throw (.invalid "generated recursor: large eliminator on a block whose sort may be Prop \
      (official: elim_only_at_universe_zero)")
  let formerTys := p.formers.map (·.type)
  let Ms ← classesNfs ops fe p formerTys tbl Ms
  let ctors ← classesCtors ops fe p formerTys rd Ms 0 Ms
  unless (rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum do
    throw (.invalid "generated recursor: the recursors' prefix has a minor premise for no \
      constructor of a class (official: invalid recursor)")
  let formerTysC ← Ms.mapM (classFormerTy ops fe p.formers)
  let elim := structElimLevel p.elim p.large
  let g0 : ClassGen := ⟨p.nP, params, Ms, formerTysC, rd.slots, ctors, elim, []⟩
  let pre ← unwrapOr (← g0.prefixBinders.run) (.internal "generated recursor: recursor prefix")
  let g := { g0 with pre := pre }
  let cvGs ← classRecTysOk ops fe g p.k p.recs cvRis rd.recCls
  let feR := so.ruleEnv p Ms cvGs rd.recCls fe
  so.flush
  let out ← classRecsRulesOk (so.opsRuleR feR) so.walkers fe feR g (classRecOf rd.recCls cvGs)
    cvGs rd.recCls
  so.flush
  pure out

/-- Twin of `classFeROvl`: the rule-less generated recursors pushed (a kernel
environment is persistent, so a push shares the rest). -/
def classFeROvl (p : BlockShape) (Ms : List TargetMajor) (cvGs : List ConstantVal)
    (recCls : List Nat) (fe : FEnv) : FEnv :=
  classFeR p Ms cvGs recCls fe

end Lean.Kernel.InLean
