inductive N where | z | s (n : N)

set_option backwards.match.sparseCases false
-- set_option trace.Meta.Match.match true in
-- set_option debug.skipKernelTC true
set_option trace.Meta.Match.matchEqs true
set_option pp.proofs true

def anyTwo : N → N → Bool
  | .s .z, _     => true
  | _,     .s .z => true
  | _,     _     => false

/--
info: def anyTwo.match_1.{u_1} : (motive : N → N → Sort u_1) →
  (x x_1 : N) → ((x : N) → motive N.z.s x) → ((x : N) → motive x N.z.s) → ((x x_2 : N) → motive x x_2) → motive x x_1 :=
fun motive x x_1 h_1 h_2 h_3 =>
  have cont_1 := fun x_2 =>
    N.casesOn (motive := fun x_3 => (∀ (x_4 : N), x_4 = x_3 → N.z.s = x → False) → motive x x_3) x_1
      (fun x_3 => h_3 x N.z)
      (fun n x_3 =>
        N.casesOn (motive := fun x_4 => (∀ (x_5 : N), x_5 = x_4.s → N.z.s = x → False) → motive x x_4.s) n
          (fun x_4 => h_2 x) (fun n x_4 => h_3 x n.s.s) x_3)
      x_2;
  N.casesOn (motive := fun x => ((∀ (x_2 : N), x_2 = x_1 → N.z.s = x → False) → motive x x_1) → motive x x_1) x
    (fun cont_1 => cont_1 sorry)
    (fun n cont_1 =>
      N.casesOn (motive := fun x => ((∀ (x_2 : N), x_2 = x_1 → N.z.s = x.s → False) → motive x.s x_1) → motive x.s x_1)
        n (fun cont_1 => h_1 x_1) (fun n cont_1 => cont_1 sorry) cont_1)
    cont_1
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
