def f (n : Nat) (hn : n % 2 = 1) (m : Nat) (hm : (n + m) % 2 = 1) : Nat :=
  match n with
  | 1 => 0
  | n' + 3 =>
    match m with
    | 0 => 1
    | m' + 1 => f n' (by sorry) m' (by sorry)

set_option pp.proofs true

/--
info: f.induct (motive : (n : Nat) → n % 2 = 1 → (m : Nat) → (n + m) % 2 = 1 → Prop)
  (case1 : ∀ (m : Nat) (hn : 1 % 2 = 1) (hm : (1 + m) % 2 = 1), motive 1 hn m hm)
  (case2 :
    ∀ (n' : Nat) (hn : (n' + 3) % 2 = 1) (hm : (n' + 3 + 0) % 2 = 1),
      (n' + 3 + 0) % 2 = 1 → motive n'.succ.succ.succ hn 0 hm)
  (case3 :
    ∀ (n' : Nat) (hn : (n' + 3) % 2 = 1) (m' : Nat) (hm : (n' + 3 + (m' + 1)) % 2 = 1),
      (n' + 3 + m'.succ) % 2 = 1 →
        motive n' (f.proof_1 n') m' (f.proof_2 n' m') → motive n'.succ.succ.succ hn m'.succ hm)
  (n : Nat) (hn : n % 2 = 1) (m : Nat) (hm : (n + m) % 2 = 1) : motive n hn m hm
-/
#guard_msgs in
#check f.induct
