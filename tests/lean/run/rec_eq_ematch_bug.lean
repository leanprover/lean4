inductive Nat
| Z : Nat
| S : Nat → Nat

open Nat
constant Add : Nat → Nat → Nat
axiom Add_Zero : ∀ a, Add a Z = a
axiom Zero_Add : ∀ a, Add Z a = a
axiom Add_Succ : ∀ a b, Add a (S b) = S (Add a b)
axiom Succ_Add : ∀ a b, Add (S a) b = S (Add a b)

local attribute [ematch] Add_Zero Zero_Add Add_Succ Succ_Add

open smt_tactic

lemma Add_comm : ∀ a b : Nat, Add a b = Add b a
| a Z            :=
  begin [smt]
    /- local hypothesis nat_add_comm should have been deleted -/
    add_lemmas_from_facts,
    ematch
  end
| a (S b) :=
  have ih : Add a b = Add b a, from Add_comm a b,
  begin [smt]
    /- local hypothesis nat_add_comm should have been deleted -/
    add_lemmas_from_facts,
    ematch
  end
