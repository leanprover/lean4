/-!

A micro-benchmark based on `simp_bubblesort`, designed specifically to exploit local hypotheses.
In the design of simp as of adding this benchmark local hypotheses do not get indexed but instead
all tried in sequence. Thus adding a couple of local hypotheses that are necessary to solve a
goal can be significantly slower than having theorems with the same statement tagged as `@[simp]`.

-/

axiom L : Type
axiom N : Type
axiom z : N
axiom s : N → N
axiom nil : L
axiom f : V → L → L
axiom iter : N → (L → L) → (L → L)

axiom V : Type
axiom a : V
axiom b : V
axiom c1 : V
axiom c2 : V
axiom c3 : V
axiom c4 : V
axiom c5 : V
axiom c6 : V
axiom c7 : V
axiom c8 : V
axiom c9 : V

axiom swap : f b (f a xs) = f a (f b xs)
axiom iter_zero : iter z g x = g x
axiom iter_succ : iter (s i) g x = iter i g (iter i g x)

noncomputable def steps : N := s (s (s (s (s (s (s z))))))

set_option maxHeartbeats 250000
set_option maxRecDepth 100000
set_option Elab.async false

--set_option profiler true

theorem normalized
    (h1 : f c1 = f c2)
    (h2 : f c2 = f c3)
    (h3 : f c3 = f c4)
    (h4 : f c4 = f c5)
    (h5 : f c5 = f c6)
    (h6 : f c6 = f c7)
    (h7 : f c7 = f c8)
    (h8 : f c8 = f c9)
    (h : c9 = b) :
  iter steps (f c1) (iter steps (f a) nil) =
  iter steps (f a) (iter steps (f b) nil) :=
by simp (maxSteps := 1000000) [swap, iter_zero, iter_succ, steps, *]

/-

When compared against this the above has a slowdown of approximately 3x at the time of writing this:

axiom h1 : f c1 = f c2
axiom h2 : f c2 = f c3
axiom h3 : f c3 = f c4
axiom h4 : f c4 = f c5
axiom h5 : f c5 = f c6
axiom h6 : f c6 = f c7
axiom h7 : f c7 = f c8
axiom h8 : f c8 = f c9
axiom h : c9 = b

theorem normalized2
    :
  iter steps (f c1) (iter steps (f a) nil) =
  iter steps (f a) (iter steps (f b) nil) :=
  by simp (maxSteps := 1000000) [swap, iter_zero, iter_succ, steps, h1, h2, h3, h4, h5 , h6, h7, h8,
    h]
-/
