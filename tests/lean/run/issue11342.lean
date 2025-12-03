opaque double (n : Nat) : Nat

inductive Parity : Nat -> Type
| even (n) : Parity (double n)
| odd  (n) : Parity (Nat.succ (double n))

-- set_option trace.Meta.Match.matchEqs true

partial def natToBin3 : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

/--
info: private theorem natToBin3.match_1.congr_eq_1.{u_1} : ∀ (motive : (x : Nat) → Parity x → Sort u_1) (x : Nat)
  (x_1 : Parity x) (h_1 : (x : Parity 0) → motive 0 x) (h_2 : (j : Nat) → motive (double j) (Parity.even j))
  (h_3 : (j : Nat) → motive (double j).succ (Parity.odd j)) (x_2 : Parity 0),
  x = 0 →
    x_1 ≍ x_2 →
      (match x, x_1 with
        | 0, x => h_1 x
        | .(double j), Parity.even j => h_2 j
        | .((double j).succ), Parity.odd j => h_3 j) ≍
        h_1 x_2
-/
#guard_msgs(pass trace, all) in
#print sig natToBin3.match_1.congr_eq_1
