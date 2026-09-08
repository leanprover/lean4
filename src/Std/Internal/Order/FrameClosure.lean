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
applied to. The companion family `opE r` frames the exception postcondition; the `EFrame`
combinators compose it from `op` by the structure of the exception postcondition type.
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
Hoare frame, the meet with `opE F ⊤`; it holds for every companion derived from the meet. -/
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
## Exception-channel companion combinators

An exception-channel companion `opE : R → EPred → EPred` composes from the structure of `EPred`:
the frame operator itself where the channel carries the assertion type, `EFrame.pointwise` under a
function layer, `EFrame.prod` on a product layer, and `EFrame.ignore` where the frame cannot act.
`vcgen` derives the companion for a goal by this recursion. The combinators stay applied in terms,
with `apply`/projection and `upperAdjoint` equations characterizing them.
-/

namespace EFrame

open Std.Internal.Order

/-- The frame acts pointwise under a function layer. -/
def pointwise {A : Type v} {R : Type x} {ε : Type w} (opE : R → A → A) (r : R) : (ε → A) → ε → A :=
  Function.comp (opE r)

/-- The frame acts componentwise on a product layer. -/
def prod {A : Type v} {B : Type v'} {R : Type x} (opA : R → A → A) (opB : R → B → B) (r : R) :
    A × B → A × B :=
  Prod.map (opA r) (opB r)

/-- The frame cannot act on the channel, so its companion ignores it. -/
def ignore {A : Type v} {R : Type x} : R → A → A := fun _ => id

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

instance (opE : R → A → A) [∀ r, PreservesSup (opE r)] (r : R) :
    PreservesSup (pointwise (ε := ε) opE r) :=
  instPreservesSupComp (opE r)

instance (opA : R → A → A) (opB : R → B → B)
    [∀ r, PreservesSup (opA r)] [∀ r, PreservesSup (opB r)] (r : R) :
    PreservesSup (prod opA opB r) :=
  instPreservesSupProdMap (opA r) (opB r)

instance (r : R) : PreservesSup (ignore (A := A) r) := preservesSup_id

/-- The wand of a pointwise-lifted companion is the pointwise wand. -/
theorem upperAdjoint_pointwise (opE : R → A → A) [∀ r, PreservesSup (opE r)] (r : R) (X : ε → A)
    (e : ε) :
    PreservesSup.upperAdjoint (pointwise opE r) X e = PreservesSup.upperAdjoint (opE r) (X e) :=
  PreservesSup.upperAdjoint_comp (opE r) X e

/-- The first component of a componentwise companion's wand is the component's wand. -/
theorem upperAdjoint_prod_fst (opA : R → A → A) (opB : R → B → B)
    [∀ r, PreservesSup (opA r)] [∀ r, PreservesSup (opB r)] (r : R) (E : A × B) :
    (PreservesSup.upperAdjoint (prod opA opB r) E).fst =
      PreservesSup.upperAdjoint (opA r) E.fst :=
  PreservesSup.upperAdjoint_prodMap_fst (opA r) (opB r) E

/-- The second component of a componentwise companion's wand is the component's wand. -/
theorem upperAdjoint_prod_snd (opA : R → A → A) (opB : R → B → B)
    [∀ r, PreservesSup (opA r)] [∀ r, PreservesSup (opB r)] (r : R) (E : A × B) :
    (PreservesSup.upperAdjoint (prod opA opB r) E).snd =
      PreservesSup.upperAdjoint (opB r) E.snd :=
  PreservesSup.upperAdjoint_prodMap_snd (opA r) (opB r) E

/-- The wand of the ignoring companion is the postcondition itself. -/
theorem upperAdjoint_ignore (r : R) (X : A) :
    PreservesSup.upperAdjoint (ignore (R := R) r) X = X :=
  PreservesSup.upperAdjoint_id X

end

end EFrame

end Lean.Order

end -- public section
