inductive N where | z | s (n : N)

set_option trace.Meta.Match.match true in
def anyTwo : N → N → Bool
  | .s .z, _     => true
  | _,     .s .z => true
  | _,     _     => false

/--
info: def anyTwo.match_1.{u_1} : (motive : N → N → Sort u_1) →
  (x x_1 : N) → ((x : N) → motive N.z.s x) → ((x : N) → motive x N.z.s) → ((x x_2 : N) → motive x x_2) → motive x x_1 :=
fun motive x x_1 h_1 h_2 h_3 =>
  have cont_1 :=
    anyTwo._sparseCasesOn_1 x_1 (fun n => anyTwo._sparseCasesOn_2 n (h_2 x) fun h_0 => h_3 x n.s) fun h_0 => h_3 x x_1;
  N.casesOn (motive := fun x => motive x x_1 → motive x x_1) x (fun cont_1 => cont_1)
    (fun n cont_1 =>
      N.casesOn (motive := fun x => motive x.s x_1 → motive x.s x_1) n (fun cont_1 => h_1 x_1) (fun n cont_1 => cont_1)
        cont_1)
    cont_1
-/
#guard_msgs in
#print anyTwo.match_1

#check anyTwo.match_1.splitter

inductive Parity : Nat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (Nat.succ (n + n))

partial def natToBin : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| .succ 0, _       => [true]
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

#check natToBin.match_1.splitter
