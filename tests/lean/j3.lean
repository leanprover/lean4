import macros
import tactic
using Nat

definition dvd (a b : Nat) : Bool := ∃ c, a * c = b
infix 50 | : dvd
theorem dvd_elim {a b : Nat} (H : a | b) : ∃ c, a * c = b  := H
theorem dvd_intro {a b : Nat} (c : Nat) (H : a * c = b) : a | b := exists_intro c H
set_opaque dvd true


theorem dvd_trans {a b c} (H1 : a | b) (H2 : b | c) : a | c
:= obtain (w1 : Nat) (Hw1 : a * w1 = b), from dvd_elim H1,
   obtain (w2 : Nat) (Hw2 : b * w2 = c), from dvd_elim H2,
     dvd_intro (w1 * w2)
       (calc a * (w1 * w2) = a * w1 * w2 : symm (mul_assoc a w1 w2)
                       ... = b * w2 : { Hw1 }
                       ... = c : Hw2)


definition prime p := p ≥ 2 ∧ forall m, m | p → m = 1 ∨ m = p

theorem not_prime_eq (n : Nat) (H1 : n ≥ 2) (H2 : ¬ prime n) : ∃ m, m | n ∧ m ≠ 1 ∧ m ≠ n
:= have H3 : ¬ n ≥ 2 ∨ ¬ (∀ m : Nat, m | n → m = 1 ∨ m = n),
     from (not_and _ _ ◂ H2),
   have H4 : ¬ ¬ n ≥ 2,
     from ((symm (not_not_eq _)) ◂ H1),
   obtain (m : Nat) (H5 :  ¬ (m | n → m = 1 ∨ m = n)),
     from (not_forall_elim (resolve1 H3 H4)),
   have H6 : m | n ∧ ¬ (m = 1 ∨ m = n),
     from ((not_implies _ _) ◂ H5),
   have H7 : ¬ (m = 1 ∨ m = n) ↔ (m ≠ 1 ∧ m ≠ n),
     from (not_or (m = 1) (m = n)),
   have H8 : m | n ∧ m ≠ 1 ∧ m ≠ n,
     from subst H6 H7,
   show ∃ m, m | n ∧ m ≠ 1 ∧ m ≠ n,
     from exists_intro m H8
