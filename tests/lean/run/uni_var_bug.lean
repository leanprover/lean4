import logic.eq

section
universe variable u
variables {A B : Type.{u}}
theorem foo (H : A = B) : A = B := H
theorem bar {C D : Type} (H : C = D) : C = D :=
foo H
end

universe variable u
variables {A B : Type.{u}}
theorem foo2 (H : A = B) : A = B := H
theorem bar2 {C D : Type} (H : C = D) : C = D :=
foo2 H
