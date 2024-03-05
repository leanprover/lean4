open BitVec

/-!
This is not how you should implement a `bitblast` tactic!
Relying on the simplifier to unroll the bitwise quantifier is not efficient.

A proper bitblaster is in the works.

Nevertheless this is a simple test bed for BitVec lemmas.
-/

theorem Fin.forall_eq_forall_lt (p : Fin n → Prop) [DecidablePred p] :
    (∀ (x : Fin n), p x) ↔ (∀ (x : Fin n), x < n → p x) := by
  simp

theorem Fin.forall_lt_succ (p : Fin n → Prop) [DecidablePred p] (k : Nat) :
    (∀ (x : Fin n), x < (k + 1) → p x) ↔
      if h : k < n then
        (p ⟨k, h⟩ ∧ ∀ (x : Fin n), x < k → p x)
      else
        ∀ (x : Fin n), x < k → p x := by
  constructor
  · intro w
    split <;> rename_i h
    · constructor
      · exact w ⟨k, h⟩ (by dsimp; omega)
      · intro x q
        exact w x (by omega)
    · intro x q
      exact w _ (by omega)
  · intro w x q
    split at w <;> rename_i h
    · by_cases r : x = k
      · subst r
        apply w.1
      · apply w.2
        omega
    · exact w _ (by omega)

theorem Fin.forall_lt_zero (p : Fin n → Prop) [DecidablePred p] :
    (∀ (x : Fin n), x < (0 : Nat) → p x) ↔ True :=
  ⟨fun _ => trivial, nofun⟩

macro "bitblast" : tactic => `(tactic|
  ( apply eq_of_getLsb_eq
    rw [Fin.forall_eq_forall_lt]
    repeat rw [Fin.forall_lt_succ, dif_pos (by decide)]
    rw [Fin.forall_lt_zero]
    simp [getLsb_add', addOverflow, msb_eq_getLsb_last]))

-- Examples not involving addition:
example (x : BitVec 64) :
    (x <<< 32 >>> 32) = (x.truncate 32).zeroExtend 64 := by
  bitblast

example (x : BitVec 64) : (x <<< 32) &&& (x >>> 32) = 0 := by
  bitblast

-- Examples involving addition:
-- (Notice here we are limited to small widths, because of the bad implementation.)
example (x y : BitVec 32) : (x + y) <<< 1 = (x <<< 1) + (y <<< 1) := by
  bitblast

example (x y : BitVec 32) :
    (x + y) &&& 255#32 = (x.truncate 8 + y.truncate 8).zeroExtend 32 := by
  bitblast
