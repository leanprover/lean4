/-!
Tests the strong (co)induction principles (`strong_coinduct`, `strong_induct`,
`strong_mutual_induct`) generated for predicates defined by `inductive_fixpoint`,
`coinductive_fixpoint` and the `coinductive` keyword. These strengthen the Park
(co)induction principles: recursive occurrences in the hypothesis carry the candidate
predicate joined (`∨`) with the coinductive predicate itself, respectively met (`∧`)
with the inductive predicate itself.
-/

namespace StrongCoinduction

def infseq {α : Sort u} (R : α → α → Prop) (x : α) : Prop :=
  ∃ y, R x y ∧ infseq R y
  coinductive_fixpoint

/--
info: StrongCoinduction.infseq.strong_coinduct.{u} {α : Sort u} (R : α → α → Prop) (pred : α → Prop)
  (hyp : ∀ (x : α), pred x → ∃ y, R x y ∧ (pred y ∨ infseq R y)) (x : α) : pred x → infseq R x
-/
#guard_msgs in
#check infseq.strong_coinduct

-- The `∨`-strengthening lets a proof by coinduction stop as soon as it enters the
-- coinductive predicate itself.
theorem infseq_step_into {α} {R : α → α → Prop} {x y : α} (hxy : R x y) (hy : infseq R y) :
    infseq R x := by
  apply infseq.strong_coinduct R (fun a => a = x) _ _ rfl
  intro a ha
  subst ha
  exact ⟨y, hxy, Or.inr hy⟩

end StrongCoinduction

namespace StrongInduction

def star (R : α → α → Prop) (x y : α) : Prop :=
  x = y ∨ ∃ z, R x z ∧ star R z y
  inductive_fixpoint

/--
info: StrongInduction.star.strong_induct.{u_1} {α : Sort u_1} (R : α → α → Prop) (y : α) (pred : α → Prop)
  (hyp : ∀ (x : α), (x = y ∨ ∃ z, R x z ∧ pred z ∧ star R z y) → pred x) (x : α) : star R x y → pred x
-/
#guard_msgs in
#check star.strong_induct

-- The `∧`-strengthening gives access to the inductive predicate itself in the
-- induction hypothesis.
theorem star_unfold {α} {R : α → α → Prop} {x y : α} (h : star R x y) :
    x = y ∨ ∃ z, R x z ∧ star R z y := by
  apply star.strong_induct R y (fun a => a = y ∨ ∃ z, R a z ∧ star R z y) _ x h
  intro a hab
  cases hab with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩

end StrongInduction

namespace MutualStrongCoinduction

mutual
  def f : Prop :=
    g
  coinductive_fixpoint

  def g : Prop :=
    f
  coinductive_fixpoint
end

/--
info: MutualStrongCoinduction.f.strong_coinduct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 ∨ g)
  (hyp_2 : pred_2 → pred_1 ∨ f) : pred_1 → f
-/
#guard_msgs in
#check f.strong_coinduct

/--
info: MutualStrongCoinduction.f.strong_mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 ∨ g)
  (hyp_2 : pred_2 → pred_1 ∨ f) : (pred_1 → f) ∧ (pred_2 → g)
-/
#guard_msgs in
#check f.strong_mutual_induct

/--
info: MutualStrongCoinduction.g.strong_coinduct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 ∨ g)
  (hyp_2 : pred_2 → pred_1 ∨ f) : pred_2 → g
-/
#guard_msgs in
#check g.strong_coinduct

-- A mutual block where the predicates take arguments, exercising the meet construction
-- both along the tuple of predicates and along their parameters.
mutual
  def tick (R : α → α → Prop) (x : α) : Prop :=
    ∃ y, R x y ∧ tock R y
  coinductive_fixpoint

  def tock (R : α → α → Prop) (x : α) : Prop :=
    ∃ y, R x y ∧ tick R y
  coinductive_fixpoint
end

/--
info: MutualStrongCoinduction.tick.strong_mutual_induct.{u_1} {α : Sort u_1} (R : α → α → Prop) (pred_1 pred_2 : α → Prop)
  (hyp_1 : ∀ (x : α), pred_1 x → ∃ y, R x y ∧ (pred_2 y ∨ tock R y))
  (hyp_2 : ∀ (x : α), pred_2 x → ∃ y, R x y ∧ (pred_1 y ∨ tick R y)) :
  (∀ (x : α), pred_1 x → tick R x) ∧ ∀ (x : α), pred_2 x → tock R x
-/
#guard_msgs in
#check tick.strong_mutual_induct

end MutualStrongCoinduction

namespace MixedStrongInduction

-- A mixed mutual block: the strengthening is `∧` for the inductive component and
-- `∨` for the coinductive one.
mutual
  def p : Prop :=
    ¬ q
  inductive_fixpoint

  def q : Prop :=
    ¬ p
  coinductive_fixpoint
end

/--
info: MixedStrongInduction.p.strong_mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : (pred_2 ∨ q → False) → pred_1)
  (hyp_2 : pred_2 → pred_1 ∧ p → False) : (p → pred_1) ∧ (pred_2 → q)
-/
#guard_msgs in
#check p.strong_mutual_induct

end MixedStrongInduction

namespace CoinductiveKeyword

coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a

/--
info: CoinductiveKeyword.infSeq.strong_coinduct.{u_1} {α : Sort u_1} (r : α → α → Prop) (pred : α → Prop)
  (hyp : ∀ (a : α), pred a → ∃ b, r a b ∧ (pred b ∨ infSeq r b)) (a✝ : α) : pred a✝ → infSeq r a✝
-/
#guard_msgs in
#check infSeq.strong_coinduct

end CoinductiveKeyword

namespace NoStrongForPartialFixpoint

def loop (x : Nat) : Option Nat :=
  loop (x + 1)
  partial_fixpoint

/--
error: Unknown constant `NoStrongForPartialFixpoint.loop.strong_induct`
-/
#guard_msgs in
#check loop.strong_induct

end NoStrongForPartialFixpoint
