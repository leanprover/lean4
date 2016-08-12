namespace foo
universe l
constants (A : Type.{l})

definition q (x : A) := x
definition h (x : A) : A := q x
definition g (x y : A) := h y
definition f (x y z : A) := g (g x y) z
definition d (x y z w : A) := f (f x y z) (f y z w) (f x w z)

attribute [defeq]
definition h.def (x : A) : h x = q x := rfl
attribute [defeq]
definition g.def (x y : A) : g x y = h y := rfl
attribute [defeq]
definition f.def (x y z : A) : f x y z = g (g x y) z := rfl
attribute [defeq]
definition d.def (x y z w : A) : d x y z w = f (f x y z) (f y z w) (f x w z) := rfl

print [defeq]
end foo
