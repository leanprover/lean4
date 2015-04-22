import logic

  set_option pp.universes true
  set_option pp.implicit true

section
  universe k
  parameter A : Type

  section
    universe variable l
    universe variable u
    parameter B : Type
    definition foo (a : A) (b : B) := b

    inductive mypair :=
    mk : A → B → mypair

    definition pr1' (p : mypair) : A := mypair.rec (λ a b, a) p
    definition pr2' (p : mypair) : B := mypair.rec (λ a b, b) p
    check mypair.rec

  end
  check mypair.rec
  variable a : A
  check foo num a 0
  definition pr1 (p : mypair num) : A   := mypair.rec (λ a b, a) p
  definition pr2 (p : mypair num) : num := mypair.rec (λ a b, b) p
end
