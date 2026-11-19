/-!
Functional induction through a `match` whose discriminant has a `have`-bound proof mentioning it
(#10516). The `have` cannot be generalized, so the goal is not refined by the `match`.
-/

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
info: bla.induct (motive : (a : Nat) → 0 < a → Prop) (case1 : ∀ (t : Nat) (h : 0 < t), t ≤ 1 → motive t h)
  (case2 : ∀ (a : Nat) (h : 0 < a + 1) (h_1 : ¬a + 1 ≤ 1), 0 ≠ a + 1 → motive a ⋯ → motive a.succ h) (a : Nat)
  (h : 0 < a) : motive a h
-/
#guard_msgs in
#check bla.induct

#guard_msgs (drop info) in
#check bla.induct_unfolding

theorem blub {a : Nat} {h : 0 < a} : bla a h ≤ 1 := by
  fun_induction bla <;> grind
