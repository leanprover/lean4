namespace foo
universe l
constants (A : Type.{l})

definition q (x : A) := x
definition h (x : A) : A := q x
definition g (x y : A) := h y
definition f (x y z : A) := g (g x y) z
definition d (x y z w : A) := f (f x y z) (f y z w) (f x w z)

definition h.rfl [defeq] (x : A) : h x = x := rfl
definition g.rfl [defeq] (x y : A) : g x y = y := rfl
definition f.rfl [defeq] (x y z : A) : f x y z = z := rfl
definition d.rfl [defeq] (x y z w : A) : d x y z w = z := rfl

definition h.def [defeq] (x : A) : h x = q x := rfl
definition g.def [defeq] (x y : A) : g x y = h y := rfl
definition f.def [defeq] (x y z : A) : f x y z = g (g x y) z := rfl
definition d.def [defeq] (x y z w : A) : d x y z w = f (f x y z) (f y z w) (f x w z) := rfl

-- Confirm that more recent annotations get priority
print [defeq] foo

attribute h.rfl [defeq] [priority 1001]
attribute g.rfl [defeq] [priority 1001]
attribute f.rfl [defeq] [priority 1001]
attribute d.rfl [defeq] [priority 1001]

-- Confirm that priority annotations override
print [defeq] foo

attribute h.def [defeq] [priority 1001]
attribute g.def [defeq] [priority 1001]
attribute f.def [defeq] [priority 1001]
attribute d.def [defeq] [priority 1001]

-- Confirm that most recent annotations get priority to break explicit priority ties
print [defeq] foo
end foo
