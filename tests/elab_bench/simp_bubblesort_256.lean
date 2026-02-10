/-!

A micro-benchmark for plain, mostly first-order rewriting of simp:

This uses axiom to make it independent of specific optimization (e.g.
for `Nat`).

It generates a “list” of 128 `b`s followed by 128 `a` and uses
bubble-sort to sort it and compares it against the expected output. 
-/

inductive V where | a | b
open V

axiom L : Type
axiom N : Type
axiom z : N
axiom s : N → N
axiom nil : L
axiom f : V → L → L
axiom iter : N → (L → L) → (L → L)

axiom swap : f b (f a xs) = f a (f b xs)
axiom iter_zero : iter z g x = g x
axiom iter_succ : iter (s i) g x = iter i g (iter i g x)

noncomputable def steps : N := s (s (s (s (s (s (s z))))))

set_option maxRecDepth 100000

theorem normalized:
  iter steps (f b) (iter steps (f a) nil) =
  iter steps (f a) (iter steps (f b) nil) :=
by simp (maxSteps := 1000000) only [swap, iter_zero, iter_succ, steps]
