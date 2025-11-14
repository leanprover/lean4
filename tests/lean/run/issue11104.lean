inductive N where | z | s (n : N)

set_option backwards.match.sparseCases false
-- set_option trace.Meta.Match.match true in
-- set_option debug.skipKernelTC true
set_option trace.Meta.Match.matchEqs true
set_option pp.proofs true

def anyTwo : N → N → Bool
  | .z,    .z    => false
  | .s .z, _     => true
  | _,     .s .z => true
  | _,     _     => false

/--
info: def anyTwo.match_1.{u_1} : (motive : N → N → Sort u_1) →
  (x x_1 : N) →
    (Unit → motive N.z N.z) →
      ((x : N) → motive N.z.s x) → ((x : N) → motive x N.z.s) → ((x x_2 : N) → motive x x_2) → motive x x_1 :=
fun motive x x_1 h_1 h_2 h_3 h_4 =>
  have cont_2 := fun x_2 x_3 =>
    N.casesOn (motive := fun x_4 =>
      (N.z = x_4 → N.z = x → False) → (∀ (x_6 : N), x_6 = x_4 → N.z.s = x → False) → motive x x_4) x_1
      (fun x_4 x_5 => h_4 x N.z)
      (fun n x_4 x_5 =>
        N.casesOn (motive := fun x_6 =>
          (N.z = x_6.s → N.z = x → False) → (∀ (x_8 : N), x_8 = x_6.s → N.z.s = x → False) → motive x x_6.s) n
          (fun x_6 x_7 => h_3 x) (fun n x_6 x_7 => h_4 x n.s.s) x_4 x_5)
      x_2 x_3;
  N.casesOn (motive := fun x =>
    ((N.z = x_1 → N.z = x → False) → (∀ (x_3 : N), x_3 = x_1 → N.z.s = x → False) → motive x x_1) → motive x x_1) x
    (fun cont_2 =>
      N.casesOn (motive := fun x =>
        ((N.z = x → N.z = N.z → False) → (∀ (x_3 : N), x_3 = x → N.z.s = N.z → False) → motive N.z x) → motive N.z x)
        x_1 (fun cont_2 => h_1 ()) (fun n cont_2 => cont_2 sorry sorry) cont_2)
    (fun n cont_2 =>
      N.casesOn (motive := fun x =>
        ((N.z = x_1 → N.z = x.s → False) → (∀ (x_3 : N), x_3 = x_1 → N.z.s = x.s → False) → motive x.s x_1) →
          motive x.s x_1)
        n (fun cont_2 => h_2 x_1) (fun n cont_2 => cont_2 sorry sorry) cont_2)
    cont_2
-/
#guard_msgs in
#print anyTwo.match_1

#print sig anyTwo.match_1.splitter

inductive Parity : Nat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (Nat.succ (n + n))

partial def natToBin : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| .succ 0, _       => [true]
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

#check natToBin.match_1.splitter
