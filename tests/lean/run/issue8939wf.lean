module

/-!
variant of issue8939 with well-founded recursion
(Or is this just 8938 showing up with 8939 fixed? anyways, more tests don't hurt)
-/

public axiom g : Nat → Nat → Nat
public axiom magic_dec : f - 1 < f

set_option warn.sorry false

set_option pp.proofs true
-- set_option trace.Elab.definition.wf true
-- set_option trace.Kernel true in

@[expose] public
def ackermann_fuel : (n m : Nat) → (fuel : Nat) → (h : g n m < fuel)  → Nat
| 0, m, _, _ => m+1
| n + 1, 0, f, h => ackermann_fuel n 1 (f - 1) (by sorry)
| n + 1, m + 1, f, h  =>
  ackermann_fuel n (ackermann_fuel (n + 1) m (f - 1) (by sorry)) (f - 1) (by as_aux_lemma => sorry)
termination_by _ _ fuel => fuel
decreasing_by
  -- At some point, using as_aux_lemma in decreasing_by did not work
  as_aux_lemma => sorry
  as_aux_lemma => sorry
  as_aux_lemma => sorry
  done

def ackermann_fuel'' : (n m : Nat) → (fuel : Nat) → (h : g n m < fuel)  → Nat
| 0, m, _, _ => m+1
| n + 1, 0, f, h => ackermann_fuel'' n 1 (f - 1) (by sorry)
| n + 1, m + 1, f, h  =>
  ackermann_fuel'' n (ackermann_fuel'' (n + 1) m (f - 1) (by sorry)) (f - 1) (by as_aux_lemma => sorry)
termination_by _ _ fuel => fuel
decreasing_by
  as_aux_lemma => sorry
  as_aux_lemma => sorry
  as_aux_lemma => sorry
  done

#print ackermann_fuel''._unary
