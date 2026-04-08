/-!
A micro-benchmark based on `simp_bubblesort`, designed specifically to force simp to work with a lot
of congruence to reach for a very deep concrete expression.
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

noncomputable def steps : N := s (s (s z)) -- smaller input size to focus on congr theorems

set_option maxRecDepth 100000
--set_option profiler true
set_option trace.Elab.async false

syntax "deep1(" num "," term "," term "," term ")" : term

macro_rules
  | `(deep1($n, $f, $a, $e)) =>
    match n.getNat with
    | 0 => return a
    | n + 1 => `($f deep1($(Lean.quote n), $f, $a, $e) $e)

-- Provoke regenerating simple congruence theorems unless they are cached or handled otherwise

/-
In an ideal world all of the below would be almost as fast as this, since we are just applying this
rewrite under a lot of congruence.

theorem foo :
    iter steps (f b) (iter steps (f a) nil) =
    iter steps (f a) (iter steps (f b) nil) := by
simp (maxSteps := 1000000) only [swap, iter_zero, iter_succ, steps]
-/

theorem deep_singular_simple (g : L → Unit → L) :
    deep1(1024, g, iter steps (f b) (iter steps (f a) nil), ()) =
    deep1(1024, g, iter steps (f a) (iter steps (f b) nil), ()) := by
simp (maxSteps := 1000000) only [swap, iter_zero, iter_succ, steps]

axiom g1 : L → Unit → L

theorem deep_singular_simple_const :
    deep1(1024, g1, iter steps (f b) (iter steps (f a) nil), ()) =
    deep1(1024, g1, iter steps (f a) (iter steps (f b) nil), ()) := by
simp (maxSteps := 1000000) only [swap, iter_zero, iter_succ, steps]

-- Provoke regenerating simple congruence theorems unless they are cached or handled otherwise,
-- adding `True` with the dependency on `x` here avoids a fast path in simp congruence theorem
-- generation as not all arguments are of kind fixed/eq anymore.

theorem deep_singular_prop_dep (g2 : (x : L) → (h : (fun _ => True) x) → L) :
    deep1(1024, g2, iter steps (f b) (iter steps (f a) nil), True.intro) =
    deep1(1024, g2, iter steps (f a) (iter steps (f b) nil), True.intro) := by
simp (maxSteps := 1000000) only [swap, iter_zero, iter_succ, steps]

axiom g2 : (x : L) → (h : (fun _ => True) x) → L

theorem deep_singular_prop_const_dep :
    deep1(1024, g2, iter steps (f b) (iter steps (f a) nil), True.intro) =
    deep1(1024, g2, iter steps (f a) (iter steps (f b) nil), True.intro) := by
simp (maxSteps := 1000000) only [swap, iter_zero, iter_succ, steps]
