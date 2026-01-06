set_option pp.mvars false

inductive N : Type where
| zero : N
| succ (n : N) : N

opaque double (n : N) : N := .zero

inductive Parity : N -> Type
| even (n) : Parity (double n)
| odd  (n) : Parity (N.succ (double n))

-- set_option trace.Meta.Match.matchEqs true

partial def natToBin3 : (n : N) → Parity n →  List Bool
| .zero, _             => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

/--
error: Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  n✝¹.succ = double n✝
at case `Parity.even` after processing
  (N.succ _), _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs in
partial def natToBin4 : (n : N) → Parity n →  List Bool
| .zero, _         => []
| .succ .zero, _   => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]
