-- set_option trace.Meta.FunInd true

def bla (a : Nat) (h : 0 < a) : Nat :=
  if h : a ≤ 1 then
    0
  else
    have : 0 ≠ a := by omega
    match a with
    | 0 => False.elim (by contradiction)
    | a + 1 => bla a (by omega)
termination_by structural a

/--
info: theorem bla.induct_unfolding : ∀ (motive : (a : Nat) → 0 < a → Nat → Prop),
  (∀ (t : Nat) (h : 0 < t), t ≤ 1 → motive t h 0) →
    (∀ (a : Nat) (h : 0 < a + 1) (h_1 : ¬a + 1 ≤ 1), 0 ≠ a + 1 → motive a ⋯ (bla a ⋯) → motive a.succ h (bla a ⋯)) →
      ∀ (a : Nat) (h : 0 < a), motive a h (bla a h)
-/
#guard_msgs(pass trace, all) in #print sig bla.induct_unfolding

/--
info: theorem bla.induct : ∀ (motive : (a : Nat) → 0 < a → Prop),
  (∀ (t : Nat) (h : 0 < t), t ≤ 1 → motive t h) →
    (∀ (a : Nat) (h : 0 < a + 1) (h_1 : ¬a + 1 ≤ 1), 0 ≠ a + 1 → motive a ⋯ → motive a.succ h) →
      ∀ (a : Nat) (h : 0 < a), motive a h
-/
#guard_msgs(pass trace, all) in #print sig bla.induct
