axiom A : Type
axiom B : Type

axiom A.toB : A → B
axiom B.toA : B → A

open Lean.Order

instance : PartialOrder A := sorry
-- It’s important that the CCPO instance isn't completely axiomatic, so that
-- `instCCPO.toOrder` is defeq to `instOrder`
instance : CCPO A where
  csup := sorry
  csup_spec := sorry
instance : PartialOrder B := sorry
instance : CCPO B where
  csup := sorry
  csup_spec := sorry

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
