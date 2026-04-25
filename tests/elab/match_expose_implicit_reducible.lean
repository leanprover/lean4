module

public def foo : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | x+3 => foo x

@[expose, implicit_reducible] public def bla : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | x+3 => bla x

public abbrev boo : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | _ => 7

/--
info: private def foo.match_1.{u_1} : (motive : Nat → Sort u_1) →
  (x : Nat) →
    (Unit → motive 0) → (Unit → motive 1) → (Unit → motive 2) → ((x : Nat) → motive x.succ.succ.succ) → motive x :=
fun motive x h_1 h_2 h_3 h_4 =>
  Nat.casesOn x (h_1 ()) fun n => Nat.casesOn n (h_2 ()) fun n => Nat.casesOn n (h_3 ()) fun n => h_4 n
-/
#guard_msgs in
#print foo.match_1

/--
info: @[implicit_reducible, expose] def bla.match_1.{u_1} : (motive : Nat → Sort u_1) →
  (x : Nat) →
    (Unit → motive 0) → (Unit → motive 1) → (Unit → motive 2) → ((x : Nat) → motive x.succ.succ.succ) → motive x :=
fun motive x h_1 h_2 h_3 h_4 =>
  Nat.casesOn x (h_1 ()) fun n => Nat.casesOn n (h_2 ()) fun n => Nat.casesOn n (h_3 ()) fun n => h_4 n
-/
#guard_msgs in
#print bla.match_1

/--
info: @[implicit_reducible, expose] def boo.match_1.{u_1} : (motive : Nat → Sort u_1) →
  (x : Nat) → (Unit → motive 0) → (Unit → motive 1) → (Unit → motive 2) → ((x : Nat) → motive x) → motive x :=
fun motive x h_1 h_2 h_3 h_4 =>
  dite (x = 0) (Eq.ndrec_symm (h_1 ())) fun h_1 =>
    dite (x = 1) (Eq.ndrec_symm (h_2 ())) fun h_2 => dite (x = 2) (Eq.ndrec_symm (h_3 ())) fun h_3 => h_4 x
-/
#guard_msgs in
#print boo.match_1
