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
applied to. The companion family `opE r` frames the exception postcondition; `EFrame` derives it
from `op` by the structure of the exception postcondition type.
-/

namespace Lean.Order

open Std.Internal.Order

section

variable {Pred : Type u} [CompleteLattice Pred] {EPred : Type v} {β : Type w} {R : Type x}

/-- `t` frames the resource `F` with respect to the operator `op : R → Pred → Pred` and its
exception-channel companion `opE`: `op F ·` commutes into the value postcondition of `t` while
`opE F ·` commutes into the exception postcondition. -/
def PredTrans.Frames (op : R → Pred → Pred) (opE : R → EPred → EPred)
    (t : PredTrans Pred EPred β) (F : R) : Prop :=
  ∀ (Q : β → Pred) (E : EPred),
    op F (t.apply Q E) ⊑ t.apply (fun a => op F (Q a)) (opE F E)

/-- The framed spec `vcgen` applies for `t`, when each `op r` and `opE r` preserves suprema:
framing `t` by `F` makes the wp at the two weakest footprints, `upperAdjoint (op F) ∘ Q` and
`upperAdjoint (opE F) E`, a precondition for `t.apply Q E` under `op F`. -/
theorem PredTrans.Frames.op_apply_upperAdjoint_le_apply (op : R → Pred → Pred)
    [∀ r, PreservesSup (op r)] [CompleteLattice EPred] {opE : R → EPred → EPred}
    [∀ r, PreservesSup (opE r)] {t : PredTrans Pred EPred β} {F : R}
    (hmono : t.Monotone) (hframes : t.Frames op opE F) (Q : β → Pred) (E : EPred) :
    op F (t.apply (fun a => PreservesSup.upperAdjoint (op F) (Q a))
        (PreservesSup.upperAdjoint (opE F) E)) ⊑ t.apply Q E := by
  refine PartialOrder.rel_trans (hframes _ _) ?_
  refine hmono _ _ _ _ (PreservesSup.upperAdjoint_le (opE F) E) ?_
  intro a
  exact PreservesSup.upperAdjoint_le (op F) (Q a)

/-- If `t` is conjunctive, then `t` frames `(F ⊓ ·)` when `F` holds before and after `t`, with
exceptional exits paying the frame's image `opE F ⊤`. The premise `hE` says `opE F` is itself a
Hoare frame, the meet with `opE F ⊤`; it holds for every meet-derived `EFrame` instance. -/
theorem PredTrans.Frames.of_conjunctive [CompleteLattice EPred] {t : PredTrans Pred EPred β}
    {opE : Pred → EPred → EPred} {F : Pred}
    (hmono : t.Monotone) (hconj : t.Conjunctive)
    (hF : F ⊑ t.apply (fun _ => F) (opE F ⊤))
    (hE : ∀ E, opE F ⊤ ⊓ E ⊑ opE F E) :
    t.Frames (· ⊓ ·) opE F := by
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
noncomputable def PredTrans.frameClosure (op : R → Pred → Pred) (opE : R → EPred → EPred)
    (t : PredTrans Pred EPred β) : PredTrans Pred EPred β :=
  ⟨fun Q E => ⨅ r, PreservesSup.upperAdjoint (op r) (t.apply (fun a => op r (Q a)) (opE r E))⟩

/-- Unfolding `frameClosure` through `apply`. -/
theorem PredTrans.apply_frameClosure (op : R → Pred → Pred) {opE : R → EPred → EPred}
    (t : PredTrans Pred EPred β) (Q : β → Pred) (E : EPred) :
    (t.frameClosure op opE).apply Q E =
      ⨅ r, PreservesSup.upperAdjoint (op r) (t.apply (fun a => op r (Q a)) (opE r E)) := rfl

/-- The frame closure carries monotonicity: if `t` is monotone, so is `t.frameClosure op opE`. -/
theorem PredTrans.monotone_frameClosure [CompleteLattice EPred] (op : R → Pred → Pred)
    [∀ r, PreservesSup (op r)] {opE : R → EPred → EPred} [∀ r, PreservesSup (opE r)]
    {t : PredTrans Pred EPred β} (h : t.Monotone) :
    (t.frameClosure op opE).Monotone := by
  intro post post' epost epost' hE hP
  simp only [PredTrans.apply_frameClosure]
  refine iInf_mono fun r => PreservesSup.upperAdjoint_mono _ ?_
  exact h _ _ _ _ (PreservesSup.map_mono (opE r) hE)
    (fun a => PreservesSup.map_mono (op r) (hP a))

/-- The frame rule, internalized: for families `op r` and `opE r` of supremum-preserving operators
whose resources compose by `comp` with the action laws `op (comp r r') = op r ∘ op r'` and
`opE (comp r r') = opE r ∘ opE r'`, and any predicate transformer `t`, the closure
`t.frameClosure op opE` frames every resource `F`. -/
theorem PredTrans.frameClosure_frames (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    {opE : R → EPred → EPred}
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hactE : ∀ r r' E, opE (comp r r') E = opE r (opE r' E))
    (t : PredTrans Pred EPred β) (F : R) :
    (t.frameClosure op opE).Frames op opE F := by
  intro Q E
  apply le_iInf
  intro F'
  apply PreservesSup.le_upperAdjoint (op F')
  rw [← hact F' F ((t.frameClosure op opE).apply Q E)]
  refine PartialOrder.rel_trans
    (PreservesSup.map_mono (op (comp F' F)) (iInf_le _ (comp F' F))) ?_
  refine PartialOrder.rel_trans (PreservesSup.upperAdjoint_le (op (comp F' F)) _) ?_
  apply PartialOrder.rel_of_eq
  rw [hactE F' F E]
  congr 1
  funext a
  rw [hact F' F (Q a)]

/-- Landing below the frame closure, transposed across the Galois connection:
`pre ⊑ (t.frameClosure op opE).apply Q E` holds exactly when
`op r pre ⊑ t.apply (fun a => op r (Q a)) (opE r E)` for every resource `r`. At a unit resource
(`op e = id`, `opE e = id`) the `r = e` conjunct is `pre ⊑ t.apply Q E`; the remaining conjuncts are
the frame conditions on `pre`, so a `pre` that cannot frame is forced down to the trivial `⊥`. -/
theorem PredTrans.le_frameClosure_iff (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    {opE : R → EPred → EPred}
    (t : PredTrans Pred EPred β) {Q : β → Pred} {E : EPred} {pre : Pred} :
    pre ⊑ (t.frameClosure op opE).apply Q E ↔
      ∀ r, op r pre ⊑ t.apply (fun a => op r (Q a)) (opE r E) := by
  constructor
  · intro h r
    exact PartialOrder.rel_trans
      (PreservesSup.map_mono (op r) (PartialOrder.rel_trans h (iInf_le _ r)))
      (PreservesSup.upperAdjoint_le (op r) _)
  · intro h
    apply le_iInf
    intro r
    exact PreservesSup.le_upperAdjoint (op r) (h r)

/-- Landing below the frame closure reduces to landing below the base transformer together with
framing: if `pre ⊑ t.apply Q E` and `t` frames every `op r`, then
`pre ⊑ (t.frameClosure op opE).apply Q E`. -/
theorem PredTrans.le_frameClosure (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    {opE : R → EPred → EPred}
    (t : PredTrans Pred EPred β) {Q : β → Pred} {E : EPred} {pre : Pred}
    (hframe : ∀ r : R, t.Frames op opE r)
    (hpre : pre ⊑ t.apply Q E) :
    pre ⊑ (t.frameClosure op opE).apply Q E :=
  (le_frameClosure_iff op t).mpr fun r =>
    PartialOrder.rel_trans (PreservesSup.map_mono (op r) hpre) (hframe r Q E)

/-- The frame closure lies below the base transformer, witnessed at a unit resource `e` with
`op e = id` and `opE e = id`. -/
theorem PredTrans.frameClosure_le (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    {opE : R → EPred → EPred}
    (e : R) (hunit : ∀ a, op e a = a) (hunitE : ∀ E, opE e E = E)
    (t : PredTrans Pred EPred β) (Q : β → Pred) (E : EPred) :
    (t.frameClosure op opE).apply Q E ⊑ t.apply Q E := by
  refine PartialOrder.rel_trans (iInf_le _ e) ?_
  rw [show (fun a => op e (Q a)) = Q from funext fun a => hunit (Q a), hunitE E]
  have h := PreservesSup.upperAdjoint_le (op e) (t.apply Q E)
  rwa [hunit] at h

end

/-!
## Deriving the exception-channel companion

`EFrame op EPred opE` derives the companion `opE` from `op` by the structure of `EPred`, mirroring
how the `WPMonad` instances build the exception postcondition stack: the frame acts on a channel
exactly when the channel carries the assertion type the frame acts on.
-/

/-- `opE` is the exception-channel companion of the frame operator `op` at the exception
postcondition type `EPred`. Instances derive `opE` structurally: the same `op` when `EPred` is the
assertion type itself, pointwise under a function or product layer, and the identity when the frame
cannot act. Each instance carries the supremum preservation of its `opE`. -/
class EFrame {Pred : Type u} [CompleteLattice Pred] {R : Type x} (op : R → Pred → Pred)
    (EPred : Type v) [CompleteLattice EPred] (opE : outParam (R → EPred → EPred)) : Prop where
  /-- Each `opE r` preserves suprema, so it has an upper adjoint. -/
  [preservesSup : ∀ r, PreservesSup (opE r)]

attribute [instance] EFrame.preservesSup

namespace EFrame

open Std.Internal.Order

variable {Pred : Type u} [CompleteLattice Pred] {R : Type x} {op : R → Pred → Pred}

/-- When the exception channel carries the assertion type itself, the frame acts on it as on the
value channel. -/
instance (priority := high) instDiag [∀ r, PreservesSup (op r)] : EFrame op Pred op where

/-- The frame acts pointwise under a function layer. -/
instance instFun {ε : Type v} {EPred' : Type v'} [CompleteLattice EPred']
    {opE' : R → EPred' → EPred'} [EFrame op EPred' opE'] :
    EFrame op (ε → EPred') (fun r E e => opE' r (E e)) where
  preservesSup r := {
    map_sup s := by
      funext e
      show opE' r (CompleteLattice.sup s e) = _
      rw [sup_apply, sup_apply, PreservesSup.map_sup (f := opE' r)]
      congr 1
      funext v
      apply propext
      constructor
      · rintro ⟨w, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨fun e' => opE' r (f e'), ⟨f, hf, rfl⟩, rfl⟩
      · rintro ⟨g, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨f e, ⟨f, hf, rfl⟩, rfl⟩ }

/-- The frame acts componentwise on a product layer. -/
instance instProd {A : Type v} {B : Type v'} [CompleteLattice A] [CompleteLattice B]
    {opA : R → A → A} {opB : R → B → B} [EFrame op A opA] [EFrame op B opB] :
    EFrame op (A × B) (fun r p => (opA r p.1, opB r p.2)) where
  preservesSup r := {
    map_sup s := by
      show (opA r (CompleteLattice.sup s).1, opB r (CompleteLattice.sup s).2) = _
      refine Eq.trans ?_ (Prod.mk_sup _)
      congr 1
      · rw [Prod.fst_sup, PreservesSup.map_sup (f := opA r)]
        congr 1
        funext y
        apply propext
        constructor
        · rintro ⟨w, ⟨b, hs⟩, rfl⟩
          exact ⟨opB r b, (w, b), hs, rfl⟩
        · rintro ⟨b, x, hx, heq⟩
          obtain ⟨h1, h2⟩ := Prod.mk.inj heq
          exact ⟨x.1, ⟨x.2, hx⟩, h1⟩
      · rw [Prod.snd_sup, PreservesSup.map_sup (f := opB r)]
        congr 1
        funext y
        apply propext
        constructor
        · rintro ⟨w, ⟨a, hs⟩, rfl⟩
          exact ⟨opA r a, (a, w), hs, rfl⟩
        · rintro ⟨a, x, hx, heq⟩
          obtain ⟨h1, h2⟩ := Prod.mk.inj heq
          exact ⟨x.2, ⟨x.1, hx⟩, h2⟩ }

/-- When the frame cannot act on the exception channel, its companion ignores it. -/
instance (priority := low) instIgnore {EPred : Type v} [CompleteLattice EPred] :
    EFrame op EPred (fun _ E => E) where

end EFrame

end Lean.Order

end -- public section
