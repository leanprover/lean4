set_option warn.sorry false

axiom A : Type
axiom B : Type

axiom A.toB : A → B
axiom B.toA : B → A

open Lean.Order

instance : PartialOrder A := sorry
-- It’s important that the CCPO instance isn't completely axiomatic, so that
-- `instCCPO.toOrder` is defeq to `instOrder`
instance : CCPO A where
  has_csup := sorry
instance : PartialOrder B := sorry
instance : CCPO B where
  has_csup := sorry

@[partial_fixpoint_monotone] axiom monotone_toA :
  ∀ {α} [PartialOrder α] (f : α → B), monotone f → monotone (fun x => B.toA (f x))
@[partial_fixpoint_monotone] axiom monotone_toB :
  ∀ {α} [PartialOrder α] (f : α → A), monotone f → monotone (fun x => A.toB (f x))

mutual
noncomputable def f : A := g.toA
partial_fixpoint
noncomputable def g : B := f.toB
partial_fixpoint
end

/--
info: equations:
theorem f.eq_1 : f = g.toA
-/
#guard_msgs in #print equations f
/--
info: f.fixpoint_induct (motive_1 : A → Prop) (motive_2 : B → Prop) (adm_1 : admissible motive_1)
  (adm_2 : admissible motive_2) (h_1 : ∀ (g : B), motive_2 g → motive_1 g.toA)
  (h_2 : ∀ (f : A), motive_1 f → motive_2 f.toB) : motive_1 f
-/
#guard_msgs in
#check f.fixpoint_induct
/--
info: g.fixpoint_induct (motive_1 : A → Prop) (motive_2 : B → Prop) (adm_1 : admissible motive_1)
  (adm_2 : admissible motive_2) (h_1 : ∀ (g : B), motive_2 g → motive_1 g.toA)
  (h_2 : ∀ (f : A), motive_1 f → motive_2 f.toB) : motive_2 g
-/
#guard_msgs in
#check g.fixpoint_induct
/--
info: f.mutual_fixpoint_induct (motive_1 : A → Prop) (motive_2 : B → Prop) (adm_1 : admissible motive_1)
  (adm_2 : admissible motive_2) (h_1 : ∀ (g : B), motive_2 g → motive_1 g.toA)
  (h_2 : ∀ (f : A), motive_1 f → motive_2 f.toB) : motive_1 f ∧ motive_2 g
-/
#guard_msgs in
#check f.mutual_fixpoint_induct
