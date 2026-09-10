/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.OfProp
public import Std.Internal.Order.PreservesSup
public import Std.Internal.Order.PredTrans

universe u v v' w x
@[expose] public section

set_option linter.missingDocs true

/-!
# The frame closure

The frame closure is an endomap on predicate transformers over a family of supremum-preserving
operators `op r`, one per resource `r`. It internalizes the frame rule into the transformer it is
applied to. The companion family `opE r` frames the exception postcondition; the `FrameOp` class
relates `op` to its companion, derived by the structure of the exception postcondition type.
-/

namespace Lean.Order

open Std.Internal.Order

/-- A resource action on the two postcondition channels of a `PredTrans Pred EPred`: `op` acts on
the value channel and its companion `opE` on the exception channel, both preserving suprema.
Instances derive `opE` from `op` by the structure of `EPred`: `op` itself where the channel carries
the assertion type, pointwise under a function layer, componentwise on a product layer, and the
ignoring companion where the frame cannot act. -/
class FrameOp {Pred : Type u} [CompleteLattice Pred] {R : Type x} (op : R → Pred → Pred)
    (EPred : Type v) [CompleteLattice EPred] (opE : outParam (R → EPred → EPred)) : Prop where
  /-- Each `op r` preserves suprema, so it has an upper adjoint. -/
  [preservesSup : ∀ r, PreservesSup (op r)]
  /-- Each `opE r` preserves suprema, so it has an upper adjoint. -/
  [preservesSupE : ∀ r, PreservesSup (opE r)]


namespace FrameOp

/-- The frame acts pointwise under a function layer. -/
def pointwise {A : Type v} {R : Type x} {ε : Type w} (opE : R → A → A) (r : R) : (ε → A) → ε → A :=
  Function.comp (opE r)

/-- The frame acts componentwise on a product layer. -/
def prod {A : Type v} {B : Type v'} {R : Type x} (opA : R → A → A) (opB : R → B → B) (r : R) :
    A × B → A × B :=
  Prod.map (opA r) (opB r)

/-- The frame cannot act on the channel, so its companion ignores it. -/
def ignore {A : Type v} {R : Type x} : R → A → A := fun _ => id

end FrameOp

section

variable {Pred : Type u} [CompleteLattice Pred] {R : Type x} {op : R → Pred → Pred}
  {EPred : Type v} [CompleteLattice EPred]

instance (opE : R → EPred → EPred) [∀ r, PreservesSup (opE r)] (r : R) {ε : Type w} :
    PreservesSup (FrameOp.pointwise (ε := ε) opE r) :=
  inferInstanceAs (PreservesSup (Function.comp (opE r)))

instance {B : Type v'} [CompleteLattice B] (opA : R → EPred → EPred) (opB : R → B → B)
    [∀ r, PreservesSup (opA r)] [∀ r, PreservesSup (opB r)] (r : R) :
    PreservesSup (FrameOp.prod opA opB r) :=
  inferInstanceAs (PreservesSup (Prod.map (opA r) (opB r)))

instance (r : R) : PreservesSup (FrameOp.ignore (A := EPred) r) :=
  inferInstanceAs (PreservesSup (id : EPred → EPred))

instance (priority := high) [∀ r, PreservesSup (op r)] : FrameOp op Pred op where

instance {ε : Type w} {opE : R → EPred → EPred} [FrameOp op EPred opE] :
    FrameOp op (ε → EPred) (FrameOp.pointwise opE) where
  preservesSup := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opE)
  preservesSupE :=
    haveI := FrameOp.preservesSupE (op := op) (EPred := EPred) (opE := opE)
    inferInstance

instance {B : Type v'} [CompleteLattice B]
    {opA : R → EPred → EPred} {opB : R → B → B} [FrameOp op EPred opA] [FrameOp op B opB] :
    FrameOp op (EPred × B) (FrameOp.prod opA opB) where
  preservesSup := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opA)
  preservesSupE :=
    haveI := FrameOp.preservesSupE (op := op) (EPred := EPred) (opE := opA)
    haveI := FrameOp.preservesSupE (op := op) (EPred := B) (opE := opB)
    inferInstance

@[default_instance]
instance (priority := low) [∀ r, PreservesSup (op r)] :
    FrameOp op EPred FrameOp.ignore where

end

namespace FrameOp

variable {A : Type u} {B : Type v} {R : Type x} {ε : Type w}

@[simp, grind =] theorem pointwise_apply (opE : R → A → A) (r : R) (E : ε → A) (e : ε) :
    pointwise opE r E e = opE r (E e) := rfl

@[simp, grind =] theorem prod_fst (opA : R → A → A) (opB : R → B → B) (r : R) (p : A × B) :
    (prod opA opB r p).fst = opA r p.fst := rfl

@[simp, grind =] theorem prod_snd (opA : R → A → A) (opB : R → B → B) (r : R) (p : A × B) :
    (prod opA opB r p).snd = opB r p.snd := rfl

@[simp, grind =] theorem ignore_apply (r : R) (a : A) : ignore r a = a := rfl

section

variable [CompleteLattice A] [CompleteLattice B]

theorem upperAdjoint_pointwise_apply (opE : R → A → A) [∀ r, PreservesSup (opE r)] (r : R) (X : ε → A)
    (e : ε) :
    PreservesSup.upperAdjoint (pointwise opE r) X e = PreservesSup.upperAdjoint (opE r) (X e) :=
  PreservesSup.upperAdjoint_comp_apply (opE r) X e

theorem upperAdjoint_prod_fst (opA : R → A → A) (opB : R → B → B)
    [∀ r, PreservesSup (opA r)] [∀ r, PreservesSup (opB r)] (r : R) (E : A × B) :
    (PreservesSup.upperAdjoint (prod opA opB r) E).fst =
      PreservesSup.upperAdjoint (opA r) E.fst :=
  PreservesSup.upperAdjoint_prodMap_fst (opA r) (opB r) E

theorem upperAdjoint_prod_snd (opA : R → A → A) (opB : R → B → B)
    [∀ r, PreservesSup (opA r)] [∀ r, PreservesSup (opB r)] (r : R) (E : A × B) :
    (PreservesSup.upperAdjoint (prod opA opB r) E).snd =
      PreservesSup.upperAdjoint (opB r) E.snd :=
  PreservesSup.upperAdjoint_prodMap_snd (opA r) (opB r) E

theorem upperAdjoint_ignore (r : R) (X : A) :
    PreservesSup.upperAdjoint (ignore (R := R) r) X = X :=
  PreservesSup.upperAdjoint_id X

end

end FrameOp

section

variable {Pred : Type u} [CompleteLattice Pred] {EPred : Type v} [CompleteLattice EPred]
  {β : Type w} {R : Type x} {opE : R → EPred → EPred}

/-- `t` frames the resource `F` with respect to the operator `op : R → Pred → Pred` and its
exception-channel companion: `op F ·` commutes into the value postcondition of `t` while
`opE F ·` commutes into the exception postcondition. -/
structure PredTrans.Frames (op : R → Pred → Pred) [FrameOp op EPred opE]
    (t : PredTrans Pred EPred β) (F : R) : Prop where
  /-- `op F` and its companion commute into the postcondition pair of `t`. -/
  op_apply_le_apply_op : ∀ (Q : β → Pred) (E : EPred),
    op F (t.apply Q E) ⊑ t.apply (fun a => op F (Q a)) (opE F E)

theorem PredTrans.Frames.of_conjunctive {opE : Pred → EPred → EPred} [FrameOp meet EPred opE]
    {t : PredTrans Pred EPred β} {F : Pred}
    (hmono : t.Monotone) (hconj : t.Conjunctive)
    (hF : F ⊑ t.apply (fun _ => F) (opE F ⊤))
    (hE : ∀ E, opE F ⊤ ⊓ E ⊑ opE F E) :
    t.Frames meet F := by
  constructor
  intro Q E
  refine PartialOrder.rel_trans (y := t.apply (fun _ => F) (opE F ⊤) ⊓ t.apply Q E) ?_ ?_
  · exact le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) hF) (meet_le_right _ _)
  · refine PartialOrder.rel_trans (hconj (fun _ => F) Q (opE F ⊤) E) ?_
    refine hmono _ _ _ _ (hE E) ?_
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- The **frame closure** of a predicate transformer `t` with respect to a family of
supremum-preserving operators `op r` and its exception-channel companion `opE r`: the meet over all
resources `r` of the `r`-upper-adjoint of `t` framed by `r` on both channels. It internalizes the
frame rule into any `t` (see `PredTrans.frameClosure_frames`), with no assumption on `t`. -/
noncomputable def PredTrans.frameClosure (op : R → Pred → Pred) [FrameOp op EPred opE]
    (t : PredTrans Pred EPred β) : PredTrans Pred EPred β :=
  ⟨fun Q E => ⨅ r, PreservesSup.upperAdjoint (op r) (t.apply (fun a => op r (Q a)) (opE r E))⟩

@[simp] theorem PredTrans.apply_frameClosure (op : R → Pred → Pred) [FrameOp op EPred opE]
    (t : PredTrans Pred EPred β) (Q : β → Pred) (E : EPred) :
    (t.frameClosure op).apply Q E =
      ⨅ r, PreservesSup.upperAdjoint (op r) (t.apply (fun a => op r (Q a)) (opE r E)) := rfl

theorem PredTrans.monotone_frameClosure (op : R → Pred → Pred) [FrameOp op EPred opE]
    {t : PredTrans Pred EPred β} (h : t.Monotone) :
    (t.frameClosure op).Monotone := by
  haveI := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opE)
  haveI := FrameOp.preservesSupE (op := op) (EPred := EPred) (opE := opE)
  intro post post' epost epost' hE hP
  simp only [PredTrans.apply_frameClosure]
  refine iInf_mono fun r => PreservesSup.upperAdjoint_mono _ ?_
  exact h _ _ _ _ (PreservesSup.map_mono (opE r) hE)
    (fun a => PreservesSup.map_mono (op r) (hP a))

theorem PredTrans.frameClosure_frames (op : R → Pred → Pred) [FrameOp op EPred opE]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hactE : ∀ r r' E, opE (comp r r') E = opE r (opE r' E))
    (t : PredTrans Pred EPred β) (F : R) :
    (t.frameClosure op).Frames op F := by
  haveI := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opE)
  constructor
  intro Q E
  apply le_iInf
  intro F'
  apply PreservesSup.le_upperAdjoint (op F')
  rw [← hact F' F ((t.frameClosure op).apply Q E)]
  refine PartialOrder.rel_trans
    (PreservesSup.map_mono (op (comp F' F)) (iInf_le _ (comp F' F))) ?_
  refine PartialOrder.rel_trans (PreservesSup.upperAdjoint_le (op (comp F' F)) _) ?_
  apply PartialOrder.rel_of_eq
  rw [hactE F' F E]
  congr 1
  funext a
  rw [hact F' F (Q a)]

theorem PredTrans.le_frameClosure_iff (op : R → Pred → Pred) [FrameOp op EPred opE]
    (t : PredTrans Pred EPred β) {Q : β → Pred} {E : EPred} {pre : Pred} :
    pre ⊑ (t.frameClosure op).apply Q E ↔
      ∀ r, op r pre ⊑ t.apply (fun a => op r (Q a)) (opE r E) := by
  haveI := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opE)
  constructor
  · intro h r
    exact PartialOrder.rel_trans
      (PreservesSup.map_mono (op r) (PartialOrder.rel_trans h (iInf_le _ r)))
      (PreservesSup.upperAdjoint_le (op r) _)
  · intro h
    apply le_iInf
    intro r
    exact PreservesSup.le_upperAdjoint (op r) (h r)

theorem PredTrans.le_frameClosure (op : R → Pred → Pred) [FrameOp op EPred opE]
    (t : PredTrans Pred EPred β) {Q : β → Pred} {E : EPred} {pre : Pred}
    (hframe : ∀ r : R, t.Frames op r)
    (hpre : pre ⊑ t.apply Q E) :
    pre ⊑ (t.frameClosure op).apply Q E :=
  haveI := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opE)
  (le_frameClosure_iff op t).mpr fun r =>
    PartialOrder.rel_trans (PreservesSup.map_mono (op r) hpre) ((hframe r).op_apply_le_apply_op Q E)

theorem PredTrans.frameClosure_le (op : R → Pred → Pred) [FrameOp op EPred opE]
    (e : R) (hunit : ∀ a, op e a = a) (hunitE : ∀ E, opE e E = E)
    (t : PredTrans Pred EPred β) (Q : β → Pred) (E : EPred) :
    (t.frameClosure op).apply Q E ⊑ t.apply Q E := by
  haveI := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opE)
  refine PartialOrder.rel_trans (iInf_le _ e) ?_
  rw [show (fun a => op e (Q a)) = Q from funext fun a => hunit (Q a), hunitE E]
  have h := PreservesSup.upperAdjoint_le (op e) (t.apply Q E)
  rwa [hunit] at h

end

end Lean.Order

end -- public section
