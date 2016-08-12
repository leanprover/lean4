namespace foo
universe l
constants (A : Type.{l})

definition q (x : A) := x
definition h (x : A) : A := q x
definition g (x y : A) := h y
definition f (x y z : A) := g (g x y) z
definition d (x y z w : A) := f (f x y z) (f y z w) (f x w z)

attribute [defeq]
definition h.rfl (x : A) : h x = x := rfl
attribute [defeq]
definition g.rfl (x y : A) : g x y = y := rfl
attribute [defeq]
definition f.rfl (x y z : A) : f x y z = z := rfl
attribute [defeq]
definition d.rfl (x y z w : A) : d x y z w = z := rfl

attribute [defeq]
definition h.def (x : A) : h x = q x := rfl
attribute [defeq]
definition g.def (x y : A) : g x y = h y := rfl
attribute [defeq]
definition f.def (x y z : A) : f x y z = g (g x y) z := rfl
attribute [defeq]
definition d.def (x y z w : A) : d x y z w = f (f x y z) (f y z w) (f x w z) := rfl

-- Confirm that more recent annotations get priority
print [defeq]

attribute h.rfl [defeq] [priority 1001]
attribute g.rfl [defeq] [priority 1001]
attribute f.rfl [defeq] [priority 1001]
attribute d.rfl [defeq] [priority 1001]

-- Confirm that priority annotations override
print [defeq]

attribute h.def [defeq] [priority 1001]
attribute g.def [defeq] [priority 1001]
attribute f.def [defeq] [priority 1001]
attribute d.def [defeq] [priority 1001]

-- Confirm that most recent annotations get priority to break explicit priority ties
print [defeq]
end foo
