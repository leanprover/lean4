module

import Lean
import Std.Tactic.Do
public import Std.Internal.Do
import Std.Internal.Do.Triple.SpecLemmas
public meta import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc
public meta import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProcAttr
public meta import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction

set_option mvcgen.warning false

open Lean.Order

section InDyLean

section ExecTrace

public
inductive Trace (α: Type) where
  | nil: Trace α
  | snoc: Trace α -> α -> Trace α

public
inductive Trace.le {α: Type} : Trace α -> Trace α -> Prop where
  | equal: (tr: Trace α) -> Trace.le tr tr
  | extend: (tr1: Trace α) -> (tr2: Trace α) -> (e: α) -> Trace.le tr1 tr2 -> Trace.le tr1 (.snoc tr2 e)

public
instance {α: Type}: LE (Trace α) where
  le := Trace.le

@[refl]
public
theorem Trace.le_refl
  {α: Type}
  (tr: Trace α)
  : tr ≤ tr
:=
  Trace.le.equal tr

grind_pattern Trace.le_refl => tr ≤ tr

public
theorem Trace.le_trans
  {α: Type}
  (tr1 tr2 tr3: Trace α)
  : tr1 ≤ tr2 → tr2 ≤ tr3 → tr1 ≤ tr3
:= by
  intros hxy hyz
  induction hyz with
  | equal => exact hxy
  | extend tr3 e _ ih =>
    exact (Trace.le.extend tr1 tr3 e ih)

public
class ExecTraceTypes where
  ExecT: Type

public
opaque ExecTraceEntry [ExecTraceTypes]: Type

public
abbrev ExecTrace [ExecTraceTypes] := Trace ExecTraceEntry

end ExecTrace

section Monad

@[expose]
public
def Traceful [ExecTraceTypes] (a: Type) := (trIn: ExecTrace) → Option a × { trOut: ExecTrace // trIn ≤ trOut }

public
instance [ExecTraceTypes]: Monad Traceful where
  pure x := fun tr => (some x, ⟨ tr, by grind ⟩)
  bind x f := fun tr =>
    let (xOptVal, trMid) := x tr
    match xOptVal with
    | none => (none, trMid)
    | some xVal =>
      let (optRes, trOut) := f xVal trMid.val
      (optRes, ⟨ trOut.val, by grind [Trace.le_trans] ⟩)

public
instance [ExecTraceTypes]: Alternative Traceful where
  failure := fun tr => (none, ⟨ tr, by grind ⟩)
  orElse x y := fun tr =>
    let (xOptVal, trMid) := x tr
    match xOptVal with
    | some xVal => (some xVal, trMid)
    | none =>
      let (optRes, trOut) := y () trMid.val
      (optRes, ⟨ trOut.val, by grind [Trace.le_trans] ⟩)

public
def Traceful.run [ExecTraceTypes] (x: Traceful a) (tr: ExecTrace): (Option a × { trOut: ExecTrace // tr ≤ trOut}) :=
  x tr

public
def Traceful.mk [ExecTraceTypes] {α: Type} (f: (tr: ExecTrace) → (Option α × { trOut: ExecTrace // tr ≤ trOut})): Traceful α :=
  f

@[expose]
public
def Err := OptionT Id
deriving Monad, Alternative

public
instance [ExecTraceTypes]: MonadLift Err Traceful := {
  monadLift x := Traceful.mk fun tr => (x, ⟨ tr, by grind ⟩ )
}

public
theorem Traceful.run_mk
  [ExecTraceTypes] {α: Type}
  (f: (tr: ExecTrace) → (Option α × { trOut: ExecTrace // tr ≤ trOut}))
  : Traceful.run (Traceful.mk f) = f
:= by
  rfl

public
theorem Traceful.run_pure
  [ExecTraceTypes]
  (x: a) (tr: ExecTrace)
  : Traceful.run (pure x) tr = (some x, ⟨ tr, by grind ⟩)
:= by
  rfl

public
theorem Traceful.run_bind
  [ExecTraceTypes]
  (x: Traceful a) (f: a → Traceful b) (tr: ExecTrace)
  : Traceful.run (x >>= f) tr = (
    let (opt_x, tr) := x.run tr
    match opt_x with
    | some x =>
      let (opt_y, tr) := (f x).run tr
      (opt_y, ⟨ tr.val, by grind [Trace.le_trans]⟩)
    | none => (none, tr)
  )
:= by
  simp [Traceful.run, Bind.bind]
  grind

public
theorem Traceful.run_failure
  [ExecTraceTypes]
  (tr: ExecTrace)
  : Traceful.run (failure: Traceful a) tr = (none, ⟨ tr, by grind ⟩)
:= by
  rfl

public
instance [ExecTraceTypes]: LawfulMonad Traceful :=
  LawfulMonad.mk' Traceful
    (id_map := by
      intro _ x
      funext s
      simp only [Functor.map, Function.comp_apply, id_eq]
      obtain ⟨o, t⟩ := x s
      cases o <;> rfl
    )
    (pure_bind := by
      simp [pure, bind]
      intro _ _ x f
      funext tr
      obtain ⟨o, t⟩ := f x tr
      rfl
    )
    (bind_assoc := by
      intro _ _ _ x f g
      simp only [bind]
      funext
      grind
    )

end Monad

section Proof

public
class ProofTraceTypes [ExecTraceTypes] where
  ProofT: Type

public
opaque ProofTraceEntry [ExecTraceTypes] [ProofTraceTypes]: Type

public
abbrev ProofTrace [ExecTraceTypes] [ProofTraceTypes] := Trace ProofTraceEntry

public axiom Trace.erase [ExecTraceTypes] [ProofTraceTypes]: ProofTrace → ExecTrace
public opaque Trace.Invariant [ExecTraceTypes] [ProofTraceTypes]: ProofTrace → Prop

end Proof

end InDyLean

section MvcgenSetup

variable [ExecTraceTypes] [ProofTraceTypes]

open Std.Internal.Do
open Lean.Order

public
structure TraceProp where
  val: { tr: ProofTrace // tr.Invariant } → Prop

public
instance: CoeFun TraceProp (fun _ => { tr: ProofTrace // tr.Invariant } → Prop) where
  coe x := x.val

public
instance: Assertion TraceProp where
  rel p1 p2 := ∀ tr, p1 tr → p2 tr
  rel_refl := by grind
  rel_trans := by grind
  rel_antisymm {p1 p2} _ _ := by cases p1; cases p2; simp only [TraceProp.mk.injEq]; funext; grind
  has_sup c := ⟨
    ⟨ fun tr => ∃ p, c p ∧ p tr ⟩,
    by
      dsimp only [Lean.Order.is_sup]
      grind
  ⟩

@[simp]
theorem my_meet_apply
  (p1 p2: TraceProp) (tr: { tr: ProofTrace // tr.Invariant })
  : (p1 ⊓ p2) tr = (p1 tr ∧ p2 tr)
:= by
  apply propext
  constructor
  · intro h
    exact ⟨meet_le_left p1 p2 tr h, meet_le_right p1 p2 tr h⟩
  · rintro ⟨h1, h2⟩
    exact le_meet (⟨fun z => z = tr⟩ : TraceProp) p1 p2
      (fun z hz => hz.symm ▸ h1) (fun z hz => hz.symm ▸ h2) tr rfl

theorem trace_sup_apply (s : TraceProp → Prop) (tr : { tr: ProofTrace // tr.Invariant }) :
    (CompleteLattice.sup s) tr = ∃ p, s p ∧ p tr := by
  apply propext
  constructor
  · intro h
    exact (sup_le s (x := (⟨fun tr => ∃ p, s p ∧ p tr⟩ : TraceProp))
      (fun p hp tr' hptr => ⟨p, hp, hptr⟩)) tr h
  · rintro ⟨p, hp, hptr⟩
    exact le_sup s hp tr hptr

instance (r : TraceProp): Lean.Order.PreservesSup (Lean.Order.meet r) where
  map_sup s := by
    apply PartialOrder.rel_antisymm <;> intro tr h
    · rw [my_meet_apply] at h
      obtain ⟨hr, hsup⟩ := h
      rw [trace_sup_apply] at hsup
      obtain ⟨p, hp, hptr⟩ := hsup
      rw [trace_sup_apply]
      exact ⟨meet r p, ⟨p, hp, rfl⟩, by rw [my_meet_apply]; exact ⟨hr, hptr⟩⟩
    · rw [trace_sup_apply] at h
      obtain ⟨y, ⟨x, hx, rfl⟩, hytr⟩ := h
      rw [my_meet_apply] at hytr
      rw [my_meet_apply, trace_sup_apply]
      exact ⟨hytr.1, ⟨x, hx, hytr.2⟩⟩

public
instance: WPMonad Traceful TraceProp EPost⟨⟩ where
  toWP α := {
    wpTrans f := ⟨fun post _epost => ⟨
      fun trProof =>
        let (optRes, trOut) := f.run trProof.val.erase
        ∃ trOutProof: ProofTrace,
        trOutProof.erase = trOut ∧
        trProof ≤ trOutProof ∧
        ∃ h: trOutProof.Invariant, -- `∃` is used to create a dependent version of `∧`
        match optRes with
        | none => True
        | some res => post res ⟨ trOutProof, h ⟩
    ⟩⟩

    wp_trans_monotone x := by
      simp only [Std.Internal.Do.PredTrans.monotone, Lean.Order.PartialOrder.rel]
      grind
  }

  pure_le_wp_pure x := by
    simp only [wp, Lean.Order.PartialOrder.rel, Traceful.run_pure]
    grind
  bind_le_wp_bind x f := by
    simp only [wp, Lean.Order.PartialOrder.rel, Traceful.run_bind]
    grind [Trace.le_trans]

end MvcgenSetup

section TestSetup

-- below is stuff in DyLean
opaque Label: Type
opaque Bytes: Type
axiom Label.pub: Label
axiom Label.secret: Label
axiom Bytes.label [ExecTraceTypes] [ProofTraceTypes]: Bytes → ProofTrace → Label
opaque Bytes.Publishable [ExecTraceTypes] [ProofTraceTypes]: Bytes → ProofTrace → Prop

-- this is not in DyLean, but I am thinking of adding it.
-- it would appear in post-conditions
def Always {α: Type} (p: Trace α → Prop) (tr: Trace α): Prop :=
  ∀ tr', tr ≤ tr' → p tr'

def Always' [ExecTraceTypes] [ProofTraceTypes] (p: ProofTrace → Prop): TraceProp := ⟨
  fun ⟨ tr, _ ⟩ => ∀ tr', tr ≤ tr' → p tr'
⟩

theorem Always_implies_self
  {α: Type} (p: Trace α → Prop) (tr: Trace α)
  : Always p tr →
    p tr
:= by grind [Always]

grind_pattern Always_implies_self => Always p tr

theorem Always'_implies_self
  [ExecTraceTypes] [ProofTraceTypes]
  (p: ProofTrace → Prop) (tr: ProofTrace) (h_inv: tr.Invariant)
  : Always' p ⟨ tr, h_inv ⟩ →
    p tr
:= by
  grind [Always']

grind_pattern Always'_implies_self => Always' p ⟨ tr, h_inv ⟩

open Std.Internal.Do
open Lean.Order

theorem always_frame
  [ExecTraceTypes] [ProofTraceTypes]
  {α: Type}
  (f: Traceful α)
  (p: ProofTrace → Prop)
  : WP.Frames Lean.Order.meet f (Always' p)
where
  conj_wp_le_wp_conj Q E := by
    simp only [PartialOrder.rel, my_meet_apply, and_imp, Subtype.forall]
    dsimp only [wp, Always', WP.wpTrans]
    simp [my_meet_apply]
    grind [Trace.le_trans]

grind_pattern always_frame => WP.Frames Lean.Order.meet f (Always' p)

@[simp]
theorem always_meet
  [ExecTraceTypes] [ProofTraceTypes]
  (p1 p2: ProofTrace → Prop)
  : Always' p1 ⊓ Always' p2 = Always' (fun tr => p1 tr ∧ p2 tr)
:= by
  apply PartialOrder.rel_antisymm <;> intro ⟨t, inv⟩ h
  · rw [my_meet_apply] at h
    exact fun tr' hle => ⟨h.1 tr' hle, h.2 tr' hle⟩
  · rw [my_meet_apply]
    exact ⟨fun tr' hle => (h tr' hle).1, fun tr' hle => (h tr' hle).2⟩

grind_pattern always_meet => Always' p1 ⊓ Always' p2

section DyLeanFrameProc
open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- Collect the `Always'` conjuncts of a precondition, descending through `⊓`. These are the frames
that transport to any extension of the current trace. -/
public meta partial def collectAlways (e : Expr) : Array Expr :=
  if e.isAppOf ``Lean.Order.meet then
    collectAlways e.appFn!.appArg! ++ collectAlways e.appArg!
  else if e.isAppOf ``Always' then
    #[e]
  else
    #[]

/-- Frame inference for `Traceful`: gather the precondition's `Always' pᵢ` conjuncts and frame by a
single `Always'` over their conjunction, `Always' (fun tr => p₁ tr ∧ … ∧ pₙ tr)`. -/
public meta def dyLeanFrameProc : FrameInferenceProc := fun _R pre _info _specPre => do
  match (collectAlways pre).toList with
  | [] => return none
  | [single] => return some single
  | a :: rest =>
    let preds := (a :: rest).map (·.appArg!)
    let domTy := (← Meta.inferType preds.head!).bindingDomain!
    let combined ← Meta.withLocalDeclD `tr domTy fun tr => do
      let last :: initRev := (preds.map (fun p => (mkApp p tr).headBeta)).reverse | unreachable!
      Meta.mkLambdaFVars #[tr] (initRev.foldl (fun acc x => mkApp (mkApp (mkConst ``And) x) acc) last)
    return some (← shareCommon (mkApp a.appFn! combined))

@[frameproc] public meta def dyLeanFP : FrameProc where
  prog := ``Traceful
  mkOpAppM := fun info => Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
  resourceTy := fun info => pure info.Pred
  op := { head := ``Lean.Order.meet }
  proc := some dyLeanFrameProc
end DyLeanFrameProc

variable [ExecTraceTypes]

-- DyLean has these functions
axiom sendMessage (b: Bytes): Traceful Nat
axiom receiveMessage (handle: Nat): Traceful Bytes
axiom genRand (size: Nat): Traceful Bytes

-- only for the tests
axiom skip: Traceful Unit
axiom requireRandJustGenerated (b: Bytes): Traceful Unit
axiom requireLabelPub (b: Bytes): Traceful Unit
axiom requireLabelSecret (b: Bytes): Traceful Unit

variable [ProofTraceTypes]

@[spec]
axiom receiveMessage.spec
  (handle: Nat)
  : Std.Internal.Do.Triple
      (receiveMessage handle)
      (⊤)
      (fun msg => Always' (fun tr => msg.Publishable tr) )
      epost⟨⟩

@[spec]
axiom sendMessage.spec
  (msg: Bytes)
  : Std.Internal.Do.Triple
      (sendMessage msg)
      (⟨fun tr => msg.Publishable tr.val⟩)
      (fun _ => ⊤)
      epost⟨⟩

@[spec_invariant_type]
structure RandUsageAndLabel where
  usage: String
  label: Bytes → Label

opaque RandGeneratedLast: ProofTrace → Bytes → Prop

@[spec]
axiom genRand.spec
  (size: Nat) (usageAndLabel: RandUsageAndLabel)
  : Std.Internal.Do.Triple
      (genRand size)
      (⟨ fun _ => True ⟩)
      (fun res => Always' (fun tr => res.label tr = usageAndLabel.label res) ⊓
        ⟨ fun tr => RandGeneratedLast tr.val res ⟩)
      epost⟨⟩

@[spec]
axiom skip.spec
  : Std.Internal.Do.Triple
      (skip)
      (⟨ fun _ => True ⟩)
      (fun _ => ⟨ fun _ => True ⟩)
      epost⟨⟩

@[spec]
axiom requireRandJustGenerated.spec
  (msg: Bytes)
  : Std.Internal.Do.Triple
      (requireRandJustGenerated msg)
      (⟨ fun tr => RandGeneratedLast tr.val msg ⟩)
      (fun _ => ⟨ fun _ => True ⟩)
      epost⟨⟩

@[spec]
axiom requireLabelPub.spec
  (msg: Bytes)
  : Std.Internal.Do.Triple
      (requireLabelPub msg)
      (⟨ fun tr => msg.label tr.val = Label.pub ⟩)
      (fun _  => ⟨ fun _ => True ⟩ )
      epost⟨⟩

@[spec]
axiom requireLabelSecret.spec
  (msg: Bytes)
  : Std.Internal.Do.Triple
      (requireLabelSecret msg)
      (⟨ fun tr => msg.label tr.val = Label.secret ⟩)
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩

end TestSetup

section Test

variable [ExecTraceTypes]

noncomputable
def testNoNeedToFrame (handle: Nat): Traceful Nat := do
  let msg ← receiveMessage handle
  sendMessage msg

noncomputable
def testFrameSimple (handle: Nat): Traceful Nat := do
  let msg ← receiveMessage handle
  skip
  sendMessage msg

noncomputable
def testNotAlways: Traceful Unit := do
  let buf ← genRand 32
  requireRandJustGenerated buf

noncomputable
def testGhostPub: Traceful Unit := do
  let buf ← genRand 32
  requireLabelPub buf

noncomputable
def testGhostSecret: Traceful Unit := do
  let buf ← genRand 32
  requireLabelSecret buf

noncomputable
def testMixed (handle: Nat): Traceful Unit := do
  let msg ← receiveMessage handle
  let buf ← genRand 32
  requireRandJustGenerated buf
  skip
  skip
  skip
  skip
  let _ ← sendMessage msg
  requireLabelPub buf

noncomputable
def testBench10: Traceful Unit := do
  let msg0 ← receiveMessage 0
  let msg1 ← receiveMessage 1
  let msg2 ← receiveMessage 2
  let msg3 ← receiveMessage 3
  let msg4 ← receiveMessage 4
  let msg5 ← receiveMessage 5
  let msg6 ← receiveMessage 6
  let msg7 ← receiveMessage 7
  let msg8 ← receiveMessage 8
  let msg9 ← receiveMessage 9
  let _ ← sendMessage msg0
  let _ ← sendMessage msg1
  let _ ← sendMessage msg2
  let _ ← sendMessage msg3
  let _ ← sendMessage msg4
  let _ ← sendMessage msg5
  let _ ← sendMessage msg6
  let _ ← sendMessage msg7
  let _ ← sendMessage msg8
  let _ ← sendMessage msg9

noncomputable
def testBench40: Traceful Unit := do
  let msg0 ← receiveMessage 0
  let msg1 ← receiveMessage 1
  let msg2 ← receiveMessage 2
  let msg3 ← receiveMessage 3
  let msg4 ← receiveMessage 4
  let msg5 ← receiveMessage 5
  let msg6 ← receiveMessage 6
  let msg7 ← receiveMessage 7
  let msg8 ← receiveMessage 8
  let msg9 ← receiveMessage 9
  let msg10 ← receiveMessage 10
  let msg11 ← receiveMessage 11
  let msg12 ← receiveMessage 12
  let msg13 ← receiveMessage 13
  let msg14 ← receiveMessage 14
  let msg15 ← receiveMessage 15
  let msg16 ← receiveMessage 16
  let msg17 ← receiveMessage 17
  let msg18 ← receiveMessage 18
  let msg19 ← receiveMessage 19
  let msg20 ← receiveMessage 20
  let msg21 ← receiveMessage 21
  let msg22 ← receiveMessage 22
  let msg23 ← receiveMessage 23
  let msg24 ← receiveMessage 24
  let msg25 ← receiveMessage 25
  let msg26 ← receiveMessage 26
  let msg27 ← receiveMessage 27
  let msg28 ← receiveMessage 28
  let msg29 ← receiveMessage 29
  let msg30 ← receiveMessage 30
  let msg31 ← receiveMessage 31
  let msg32 ← receiveMessage 32
  let msg33 ← receiveMessage 33
  let msg34 ← receiveMessage 34
  let msg35 ← receiveMessage 35
  let msg36 ← receiveMessage 36
  let msg37 ← receiveMessage 37
  let msg38 ← receiveMessage 38
  let msg39 ← receiveMessage 39
  let _ ← sendMessage msg0
  let _ ← sendMessage msg1
  let _ ← sendMessage msg2
  let _ ← sendMessage msg3
  let _ ← sendMessage msg4
  let _ ← sendMessage msg5
  let _ ← sendMessage msg6
  let _ ← sendMessage msg7
  let _ ← sendMessage msg8
  let _ ← sendMessage msg9
  let _ ← sendMessage msg10
  let _ ← sendMessage msg11
  let _ ← sendMessage msg12
  let _ ← sendMessage msg13
  let _ ← sendMessage msg14
  let _ ← sendMessage msg15
  let _ ← sendMessage msg16
  let _ ← sendMessage msg17
  let _ ← sendMessage msg18
  let _ ← sendMessage msg19
  let _ ← sendMessage msg20
  let _ ← sendMessage msg21
  let _ ← sendMessage msg22
  let _ ← sendMessage msg23
  let _ ← sendMessage msg24
  let _ ← sendMessage msg25
  let _ ← sendMessage msg26
  let _ ← sendMessage msg27
  let _ ← sendMessage msg28
  let _ ← sendMessage msg29
  let _ ← sendMessage msg30
  let _ ← sendMessage msg31
  let _ ← sendMessage msg32
  let _ ← sendMessage msg33
  let _ ← sendMessage msg34
  let _ ← sendMessage msg35
  let _ ← sendMessage msg36
  let _ ← sendMessage msg37
  let _ ← sendMessage msg38
  let _ ← sendMessage msg39

open Std.Internal.Do

variable [ProofTraceTypes]

@[grind .]
theorem blah : Always' p ⊓ Always' q ⊑ Always' (fun tr => p tr ∧ q tr) := by
  simp only [always_meet]
  rfl

@[grind .]
theorem blah2 : p ⊑ Always' (fun _ => True) := by
  intro _ _ _ _
  trivial

@[grind ←]
theorem blah3 (h : ∀ tr, p tr.val → q tr) : Always' p ⊑ q := by
  simp only [PartialOrder.rel, Always']
  grind

@[grind ←]
theorem blah4 (h : ∀ tr', tr.val ≤ tr' → p tr') : (Always' p).val tr := by
  grind [Always']

/-- `Always' p` at a trace unfolds to a statement over all future traces; makes it transparent to `grind`. -/
@[grind =]
theorem always'_val {p : ProofTrace → Prop} (tr : { t : ProofTrace // t.Invariant }) :
    (Always' p).val tr = ∀ tr', tr.val ≤ tr' → p tr' := by
  obtain ⟨t, inv⟩ := tr; rfl

@[grind ←]
theorem blah5 {p q : TraceProp} (h : ∀ tr, p.val tr → q.val tr) : p ⊑ q := by
  simp only [PartialOrder.rel]
  grind

theorem testNoNeedToFrame.spec
  (handle: Nat)
  : Std.Internal.Do.Triple
      (testNoNeedToFrame handle)
      (⟨ fun _ => True ⟩ )
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩
:= by vcgen [testNoNeedToFrame] with finish

set_option tactic.hygienic false

-- The frame VCs discharge through `always_frame`/`Always'_implies_self` and the `⊓` lemmas above; the
-- proc frames every `Always'`-carrying call (even where redundant), so each spec's discharger runs the
-- robust `try dsimp/intro/simp at pre; grind` sweep over the resulting frame side goals.
theorem testFrameSimple.spec
  (handle: Nat)
  : Std.Internal.Do.Triple
      (testFrameSimple handle)
      (⟨ fun _ => True ⟩ )
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩
:= by
  vcgen [testFrameSimple]
  all_goals try dsimp only [Lean.Order.PartialOrder.rel]
  all_goals try intro ⟨ tr, h_inv ⟩ pre
  all_goals try simp at pre
  all_goals grind

theorem testNotAlways.spec
  : Std.Internal.Do.Triple
      (testNotAlways)
      (⟨ fun _ => True ⟩)
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩
:= by
  vcgen [testNotAlways] invariants
  | inv1 => ⟨ "toto", fun _ => Label.pub ⟩
  all_goals try dsimp only [Lean.Order.PartialOrder.rel]
  all_goals try intro ⟨ tr, h_inv ⟩ pre
  all_goals try simp only [my_meet_apply] at pre
  all_goals grind

theorem testGhostPub.spec
  : Std.Internal.Do.Triple
      (testGhostPub)
      (⟨ fun _ => True ⟩)
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩
:= by
  vcgen [testGhostPub] invariants
  | inv1 => ⟨"toto", fun _ => Label.pub⟩
  all_goals try dsimp only [Lean.Order.PartialOrder.rel]
  all_goals try intro ⟨ tr, h_inv ⟩ pre
  all_goals try simp at pre
  all_goals grind

theorem testGhostSecret.spec
  : Std.Internal.Do.Triple
      (testGhostSecret)
      (⟨ fun _ => True ⟩ )
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩
:= by
  vcgen [testGhostSecret] invariants
  | inv1 => ⟨"toto", fun _ => Label.secret⟩
  all_goals try dsimp only [Lean.Order.PartialOrder.rel]
  all_goals try intro ⟨ tr, h_inv ⟩ pre
  all_goals try simp at pre
  all_goals grind

theorem testMixed.spec
  (handle: Nat)
  : Std.Internal.Do.Triple
      (testMixed handle)
      (⟨ fun _ => True ⟩)
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩
:= by
  vcgen [testMixed] invariants
  | inv1 => ⟨"toto", fun _ => Label.pub⟩
  with try finish
  all_goals try dsimp only [Lean.Order.PartialOrder.rel]
  all_goals try intro ⟨ tr, h_inv ⟩ pre
  all_goals try simp only [my_meet_apply] at pre
  all_goals grind

theorem testBench10.spec
  : Std.Internal.Do.Triple
      (testBench10)
      (⟨ fun _ => True ⟩)
      (fun _  => ⟨ fun _ => True ⟩)
      epost⟨⟩
:= by
  vcgen [testBench10] with finish

-- theorem testBench40.spec
--   : Std.Internal.Do.Triple
--       (testBench40)
--       (⟨ fun _ => True ⟩)
--       (fun _  => ⟨ fun _ => True ⟩)
--       epost⟨⟩
-- := by
--   vcgen [testBench40] with finish

end Test
