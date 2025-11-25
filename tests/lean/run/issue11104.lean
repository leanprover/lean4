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
  have cont_2 := N.casesOn x_1 (h_4 x N.z) fun n => N.casesOn n (h_3 x) fun n => h_4 x n.s.s;
  N.casesOn (motive := fun x => motive x x_1 → motive x x_1) x
    (fun cont_2 =>
      N.casesOn (motive := fun x => motive N.z x → motive N.z x) x_1 (fun cont_2 => h_1 ()) (fun n cont_2 => cont_2)
        cont_2)
    (fun n cont_2 =>
      N.casesOn (motive := fun x => motive x.s x_1 → motive x.s x_1) n (fun cont_2 => h_2 x_1) (fun n cont_2 => cont_2)
        cont_2)
    cont_2
-/
#guard_msgs in
#print anyTwo.match_1

inductive Parity : Nat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (Nat.succ (n + n))

set_option match.ignoreUnusedAlts true  in
partial def natToBin : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| .succ 0, _       => [true]
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]
| _, _ => []

-- No eqns, #11342
/--
error: Failed to realize constant natToBin.match_1.splitter:
  failed to generate equality theorem `_private.lean.run.issue11104.0.natToBin.match_1.eq_3` for `match` expression `natToBin.match_1`
  motive✝ : (x : Nat) → Parity x → Sort u_1
  j✝ : Nat
  h_1✝ : (x : Parity 0) → motive✝ 0 x
  h_2✝ : (x : Parity (Nat.succ 0)) → motive✝ 1 x
  h_3✝ : (j : Nat) → motive✝ (j + j) (Parity.even j)
  h_4✝ : (j : Nat) → motive✝ (j + j).succ (Parity.odd j)
  h_5✝ : (x : Nat) → (x_1 : Parity x) → motive✝ x x_1
  x✝¹ : ∀ (x : Parity 0), j✝ + j✝ = 0 → Parity.even j✝ ≍ x → False
  x✝ : ∀ (x : Parity (Nat.succ 0)), j✝ + j✝ = 1 → Parity.even j✝ ≍ x → False
  ⊢ Nat.rec (motive := fun x => (x_1 : Parity x) → motive✝ x x_1 → motive✝ x x_1) (fun x cont_2 => h_1✝ x)
        (fun n n_ih =>
          (fun n x cont_2 =>
              Nat.casesOn (motive := fun x => (x_1 : Parity x.succ) → motive✝ x.succ x_1 → motive✝ x.succ x_1) n
                (fun x cont_2 => h_2✝ x) (fun n x cont_2 => cont_2) x cont_2)
            n)
        (j✝ + j✝) (Parity.even j✝)
        ((fun x =>
            Parity.casesOn (motive := fun a x => j✝ + j✝ = a → Parity.even j✝ ≍ x → motive✝ (j✝ + j✝) (Parity.even j✝))
              x
              (fun n h =>
                Eq.ndrec (motive := fun x => (x_1 : Parity x) → x_1 ≍ Parity.even n → motive✝ x x_1)
                  (fun x h => Eq.symm (eq_of_heq h) ▸ h_3✝ n) (Eq.symm h) (Parity.even j✝))
              fun n h =>
              Eq.ndrec (motive := fun x => (x_1 : Parity x) → x_1 ≍ Parity.odd n → motive✝ x x_1)
                (fun x h => Eq.symm (eq_of_heq h) ▸ h_4✝ n) (Eq.symm h) (Parity.even j✝))
          (Parity.even j✝) (Eq.refl (j✝ + j✝)) (HEq.refl (Parity.even j✝))) =
      h_3✝ j✝
---
error: Unknown constant `natToBin.match_1.splitter`
-/
#guard_msgs(pass trace, all) in
#print sig natToBin.match_1.splitter

partial def natToBin2 : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| .succ 0, _       => [true]
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

#print sig natToBin2.match_1.splitter

set_option backwards.match.divide false in
partial def natToBin3 : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

#print sig natToBin3.match_1.splitter
