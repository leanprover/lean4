universes u

structure pointed :=
(carrier : Type u) (point : carrier)

instance: has_coe_to_sort pointed :=
⟨_, pointed.carrier⟩

example (p : pointed) := list p -- coercion works in argument position
example (p : pointed) : p := p.point