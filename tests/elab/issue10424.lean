set_option warn.sorry false
set_option pp.proofs true

-- set_option trace.split.failure true
-- set_option trace.split.debug true

/--
error: Tactic `split` failed: Could not split an `if` or `match` expression in the goal

Hint: Use `set_option trace.split.failure true` to display additional diagnostic information

n : Nat
⊢ Fin.last n =
    match id n with
    | 0 => Fin.last 0
    | n.succ => Fin.last (n + 1)
-/
#guard_msgs(pass trace, all) in
example (n : Nat) : Fin.last n = match (motive := ∀ n, Fin (n+1)) id n with
  | 0 => Fin.last 0
  | n + 1 => Fin.last (n + 1) := by
  split <;> rfl

-- This is the type-incorrect target after generalization

/--
error: Type mismatch
  match n with
  | 0 => Fin.last 0
  | n.succ => Fin.last (n + 1)
has type
  Fin (n + 1)
but is expected to have type
  Fin (n0 + 1)
---
error: (kernel) declaration has metavariables '_example'
-/
#guard_msgs in
example (n0 n : Nat) (h : id n0 = n) :
  Fin.last n0 =
    match (generalizing := false) (motive := ∀ n, Fin (n + 1)) n with
    | 0 => Fin.last 0
    | .succ n => Fin.last (n + 1) := sorry

-- Maybe split could use `ndrec` to cast the result type?
-- But not sure if the result is useful

example (n0 n : Nat) (h : id n0 = n) :
  Fin.last n0 =
    h.symm.ndrec (motive := fun n => Fin (n + 1))
      (match (generalizing := false) (motive := ∀ n, Fin (n + 1)) n with
       | 0 => Fin.last 0
       | .succ n => Fin.last (n + 1)) := by
  split
  · sorry
  · sorry


-- Variant with proof-valued discriminant. This works (and always has):

example (n : Nat) (h : n > 0): Fin.last n = match (motive := ∀ n _, Fin (n+1)) n, h with
  | 0, h => by contradiction
  | n + 1, _ => Fin.last (n + 1) := by
  split
  · contradiction
  · rfl

-- This failed, non-FVar discr.
-- Succeeds now

#guard_msgs(pass trace, all) in
example (n : Nat) (hpos : n > 0): Fin.last n = match (motive := ∀ n _, Fin (n+1)) n, id hpos with
  | 0, hpos0 => by contradiction
  | n + 1, _ => Fin.last (n + 1) := by
  split
  · contradiction
  · rfl

-- It essentially manually abstracted the discr

example (n : Nat) (h : n > 0): Fin.last n = match (motive := ∀ n _, Fin (n+1)) n, id h with
  | 0, h => by contradiction
  | n + 1, _ => Fin.last (n + 1) := by
  generalize (id h) = h'
  split
  · contradiction
  · rfl
