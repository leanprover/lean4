def foo (n m : Nat) (h : n < m) : Nat :=
  match m with
  | 0 => by contradiction -- This case should not show up in the principles below
  | m+1 => match n with
    | 0 => 0
    | n+1 => foo n m (Nat.succ_lt_succ_iff.mp h)

/--
info: foo.induct (motive : (n m : Nat) → n < m → Prop) (case1 : ∀ (m : Nat) (h : 0 < m + 1), 0 < m.succ → motive 0 m.succ h)
  (case2 : ∀ (m n : Nat) (h : n + 1 < m + 1), n.succ < m.succ → motive n m ⋯ → motive n.succ m.succ h) (n m : Nat)
  (h : n < m) : motive n m h
-/
#guard_msgs in
#check foo.induct

/--
info: foo.induct_unfolding (motive : (n m : Nat) → n < m → Nat → Prop)
  (case1 : ∀ (m : Nat) (h : 0 < m + 1), 0 < m.succ → motive 0 m.succ h 0)
  (case2 :
    ∀ (m n : Nat) (h : n + 1 < m + 1), n.succ < m.succ → motive n m ⋯ (foo n m ⋯) → motive n.succ m.succ h (foo n m ⋯))
  (n m : Nat) (h : n < m) : motive n m h (foo n m h)
-/
#guard_msgs in
#check foo.induct_unfolding


/--
info: foo.fun_cases (motive : (n m : Nat) → n < m → Prop)
  (case1 : ∀ (m : Nat) (h : 0 < m + 1), 0 < m + 1 → 0 < m.succ → motive 0 m.succ h)
  (case2 : ∀ (m n : Nat) (h : n + 1 < m + 1), n.succ < m + 1 → n.succ < m.succ → motive n.succ m.succ h) (n m : Nat)
  (h : n < m) : motive n m h
-/
#guard_msgs in
#check foo.fun_cases
