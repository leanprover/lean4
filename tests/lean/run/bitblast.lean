open BitVec

/-!
This is not how you should implement a `bitblast` tactic!
Relying on the simplifier to unroll the bitwise quantifier is not efficient.

A proper bitblaster is in the works.

Nevertheless this is a simple test bed for BitVec lemmas.
-/

theorem Fin.forall_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (∀ (x : Fin (n + 1)), p x) ↔ (p (Fin.last _) ∧ ∀ (x : Fin n), p (x.castAdd 1)) :=
  ⟨fun w => ⟨w _, fun i => w _⟩, fun ⟨h, w⟩ x =>
    if p : x = Fin.last _ then by
      subst p; exact h
    else by
      -- This line is needed now that `omega` doesn't check defeq on atoms.
      simp [last, ← Fin.val_ne_iff] at p
      have t : x < n := by omega
      rw [show x = castAdd 1 ⟨x, by omega⟩ by rfl]
      apply w⟩

@[simp] theorem Fin.forall_zero (p : Fin 0 → Prop) [DecidablePred p] :
    (∀ (x : Fin 0), p x) ↔ True :=
  ⟨fun _ => trivial, nofun⟩

macro "bitblast" : tactic => `(tactic|
  (apply eq_of_getLsb_eq
   simp only [Fin.forall_succ]
   simp [getLsb_add', addOverflow, msb_eq_getLsb_last]))

-- Examples not involving addition:
example (x : BitVec 64) :
    (x <<< 32 >>> 32) = (x.truncate 32).zeroExtend 64 := by
  bitblast

example (x : BitVec 64) : (x <<< 32) &&& (x >>> 32) = 0 := by
  bitblast

-- Examples involving addition:
-- (Notice here we are limited to small widths, because of the bad implementation.)
example (x y : BitVec 16) : (x + y) <<< 1 = (x <<< 1) + (y <<< 1) := by
  bitblast

example (x y : BitVec 16) :
    (x + y) &&& 255#16 = (x.truncate 8 + y.truncate 8).zeroExtend 16 := by
  bitblast
