def f : Nat → Nat
  | 0 => 0
  | 10 => 1
  | 100 => 2
  | _ => 3


/--
info: def f.match_1.{u_1} : (motive : Nat → Sort u_1) →
  (x : Nat) → (Unit → motive 0) → (Unit → motive 10) → (Unit → motive 100) → ((x : Nat) → motive x) → motive x
-/
#guard_msgs in
#print sig f.match_1


/--
info: private def f.match_1.splitter.{u_1} : (motive : Nat → Sort u_1) →
  (x : Nat) →
    (Unit → motive 0) →
      (Unit → motive 10) →
        (Unit → motive 100) → ((x : Nat) → (x = 0 → False) → (x = 10 → False) → (x = 100 → False) → motive x) → motive x
-/
#guard_msgs in
#print sig f.match_1.splitter

/--
info: private theorem f.match_1.eq_4.{u_1} : ∀ (motive : Nat → Sort u_1) (x : Nat) (h_1 : Unit → motive 0)
  (h_2 : Unit → motive 10) (h_3 : Unit → motive 100) (h_4 : (x : Nat) → motive x),
  (x = 0 → False) →
    (x = 10 → False) →
      (x = 100 → False) →
        (match x with
          | 0 => h_1 ()
          | 10 => h_2 ()
          | 100 => h_3 ()
          | x => h_4 x) =
          h_4 x
-/
#guard_msgs in
#print sig f.match_1.eq_4
