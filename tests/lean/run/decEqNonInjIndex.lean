/-!
This test checks what deriving `DecidableEq` does when the inductive type has
non-injective indices, and just how bad the error messages are.
-/

opaque f : Nat → Nat

-- set_option trace.Elab.Deriving.decEq true
-- set_option trace.Elab.Deriving.beq true

/--
error: Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  f n✝¹ = f n✝
at case `T.mk1` after processing
  _, (T.mk1 _ _), _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
---
error: Dependent elimination failed: Failed to solve equation
  f n✝ = f n
-/
#guard_msgs(pass trace, all) in
inductive T : (n : Nat) → Type where
  | mk1 : Fin n → T (f n)
  | mk2 : Fin (2*n) → T (f n)
deriving BEq, DecidableEq
