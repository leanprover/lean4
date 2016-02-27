namespace foo
universe l
constants (A : Type.{l})

definition q (x : A) := x
definition h (x : A) : A := q x
definition g (x y : A) := h y
definition f (x y z : A) := g (g x y) z
definition d (x y z w : A) := f (f x y z) (f y z w) (f x w z)

definition h.def [defeq] (x : A) : h x = q x := rfl
definition g.def [defeq] (x y : A) : g x y = h y := rfl
definition f.def [defeq] (x y z : A) : f x y z = g (g x y) z := rfl
definition d.def [defeq] (x y z w : A) : d x y z w = f (f x y z) (f y z w) (f x w z) := rfl

print [defeq] foo
end foo
