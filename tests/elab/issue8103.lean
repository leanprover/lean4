-- set_option trace.Meta.FunInd true in
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
#guard_msgs(pass trace, all) in
#check foo.induct

/--
info: foo.induct_unfolding (motive : (n m : Nat) → n < m → Nat → Prop)
  (case1 : ∀ (m : Nat) (h : 0 < m + 1), 0 < m.succ → motive 0 m.succ h 0)
  (case2 :
    ∀ (m n : Nat) (h : n + 1 < m + 1), n.succ < m.succ → motive n m ⋯ (foo n m ⋯) → motive n.succ m.succ h (foo n m ⋯))
  (n m : Nat) (h : n < m) : motive n m h (foo n m h)
-/
#guard_msgs(pass trace, all) in
#check foo.induct_unfolding


/--
info: foo.fun_cases (motive : (n m : Nat) → n < m → Prop)
  (case1 : ∀ (m : Nat) (h : 0 < m + 1), 0 < m + 1 → 0 < m.succ → motive 0 m.succ h)
  (case2 : ∀ (m n : Nat) (h : n + 1 < m + 1), n.succ < m + 1 → n.succ < m.succ → motive n.succ m.succ h) (n m : Nat)
  (h : n < m) : motive n m h
-/
#guard_msgs(pass trace, all) in
#check foo.fun_cases

def bar (n m : Nat) (h : n = m) : Nat :=
  match m with
  | 0 => 0
  | m+1 => match n with
    | 0 => by contradiction
    | n+1 => bar n m (Nat.succ.inj h)

/--
info: bar.induct (motive : (n m : Nat) → n = m → Prop) (case1 : ∀ (h : 0 = 0), motive 0 0 h)
  (case2 : ∀ (m n : Nat) (h : n + 1 = m + 1), m.succ = n.succ → motive n m ⋯ → motive n.succ m.succ h) (n m : Nat)
  (h : n = m) : motive n m h
-/
#guard_msgs(pass trace, all) in
#check bar.induct

/--
info: bar.induct_unfolding (motive : (n m : Nat) → n = m → Nat → Prop) (case1 : ∀ (h : 0 = 0), motive 0 0 h 0)
  (case2 :
    ∀ (m n : Nat) (h : n + 1 = m + 1), m.succ = n.succ → motive n m ⋯ (bar n m ⋯) → motive n.succ m.succ h (bar n m ⋯))
  (n m : Nat) (h : n = m) : motive n m h (bar n m h)
-/
#guard_msgs(pass trace, all) in
#check bar.induct_unfolding

/--
info: bar.fun_cases (motive : (n m : Nat) → n = m → Prop) (case1 : ∀ (h : 0 = 0), motive 0 0 h)
  (case2 : ∀ (m n : Nat) (h : n + 1 = m + 1), m.succ = m + 1 → m.succ = n.succ → motive n.succ m.succ h) (n m : Nat)
  (h : n = m) : motive n m h
-/
#guard_msgs(pass trace, all) in
#check bar.fun_cases

def baz (n : Nat) (h : n ≠ 0) : Nat :=
  match n with
  | 0 => by contradiction
  | k + 1 => if h : k = 0 then 0 else baz k h


/--
info: baz.induct (motive : (n : Nat) → n ≠ 0 → Prop) (case1 : ∀ (h : 0 + 1 ≠ 0), motive (Nat.succ 0) h)
  (case2 : ∀ (k : Nat) (h : k + 1 ≠ 0) (h_1 : ¬k = 0), motive k h_1 → motive k.succ h) (n : Nat) (h : n ≠ 0) :
  motive n h
-/
#guard_msgs(pass trace, all) in
#check baz.induct

/--
info: baz.induct_unfolding (motive : (n : Nat) → n ≠ 0 → Nat → Prop) (case1 : ∀ (h : 0 + 1 ≠ 0), motive (Nat.succ 0) h 0)
  (case2 : ∀ (k : Nat) (h : k + 1 ≠ 0) (h_1 : ¬k = 0), motive k h_1 (baz k h_1) → motive k.succ h (baz k h_1)) (n : Nat)
  (h : n ≠ 0) : motive n h (baz n h)
-/
#guard_msgs(pass trace, all) in
#check baz.induct_unfolding

/--
info: baz.fun_cases (motive : (n : Nat) → n ≠ 0 → Prop) (case1 : ∀ (h : 0 + 1 ≠ 0), Nat.succ 0 ≠ 0 → motive (Nat.succ 0) h)
  (case2 : ∀ (k : Nat) (h : k + 1 ≠ 0), ¬k = 0 → k.succ ≠ 0 → motive k.succ h) (n : Nat) (h : n ≠ 0) : motive n h
-/
#guard_msgs(pass trace, all) in
#check baz.fun_cases


def mean (n m : Nat) (h : n = m) : Nat :=
  match m with
  | 0 => 0
  | m+1 => match n with
    | 0 => (by contradiction : Bool → Nat) true -- overapplied `noConfusion`
    | n+1 => Nat.noConfusion h fun h' => mean n m h' -- non-contradictory `noConfusion`

/--
info: mean.fun_cases (motive : (n m : Nat) → n = m → Prop) (case1 : ∀ (h : 0 = 0), motive 0 0 h)
  (case2 : ∀ (m n : Nat) (h : n + 1 = m + 1), m.succ = m + 1 → m.succ = n.succ → motive n.succ m.succ h) (n m : Nat)
  (h : n = m) : motive n m h
-/
#guard_msgs(pass trace, all) in
#check mean.fun_cases
