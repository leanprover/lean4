open tactic

namespace baz

theorem bar : true := trivial

meta def foo : tactic unit :=
do applyc ``bar

end baz

example : true :=
by baz.foo
