universe l
constants (A : Type.{l})

definition q (x : A) : A := x
definition h (x : A) : A := q x
definition g (x y : A) := h y
definition f (x y z : A) := g (g x y) z
definition d (x y z w : A) := f (f x y z) (f y z w) (f x w z)

definition h.def [defeq] (x : A) : h x = q x := rfl
definition g.def [defeq] (x y : A) : g x y = h y := rfl
definition f.def [defeq] (x y z : A) : f x y z = g (g x y) z := rfl
definition d.def [defeq] (x y z w : A) : d x y z w = f (f x y z) (f y z w) (f x w z) := rfl

#defeq_simplify env λ x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z))
#defeq_simplify env Π x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z)) = (λ x, x) w

set_option defeq_simplify.exhaustive false
#defeq_simplify env λ x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z))
#defeq_simplify env Π x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z)) = (λ x, x) w

set_option defeq_simplify.top_down true
#defeq_simplify env λ x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z))
#defeq_simplify env Π x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z)) = (λ x, x) w

attribute q [reducible]
set_option defeq_simplify.exhaustive true
set_option defeq_simplify.top_down false
#defeq_simplify env λ x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z))
#defeq_simplify env Π x y z w, (λ x, d x) (g (f x y z) (f z y x)) (g x z) (f y z w) (q (g x z)) = (λ x, x) w
