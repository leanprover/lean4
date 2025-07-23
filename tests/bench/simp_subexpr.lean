/-!
A micro-benchmark based on `simp_bubblesort`, designed specifically to use the subexpression
cache for rewriting in `simp`.
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
axiom combine : L → L → L

axiom swap : f b (f a xs) = f a (f b xs)
axiom iter_zero : iter z g x = g x
axiom iter_succ : iter (s i) g x = iter i g (iter i g x)

noncomputable def steps : N := s (s (s (s (s (s (s z))))))

set_option maxRecDepth 100000
set_option profiler true

syntax "tree(" num "," term "," term ")" : term

macro_rules
  | `(tree($n, $l, $r)) =>
    match n.getNat with
    | 0 => `(combine $l $r)
    | n + 1 => `(combine tree($(Lean.quote n), $l, $r) tree($(Lean.quote n), $r, $l))


-- If run with -memoize or caching fails otherwise this regresses to timeout

theorem normalized:
  tree(0, (iter steps (f a) (iter steps (f b) nil)), (iter steps (f b) (iter steps (f a) nil))) =
  tree(0, (iter steps (f b) (iter steps (f a) nil)), (iter steps (f a) (iter steps (f b) nil))) :=
by simp (maxSteps := 1000000) only [swap, iter_zero, iter_succ, steps]
