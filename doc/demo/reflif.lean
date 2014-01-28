import macros

scope
  variable A : Type
  variable R : A → A → Bool
  axiom Symm  {x y : A} : R x y → R y x
  axiom Trans {x y z : A} : R x y → R y z → R x z

  theorem ReflIf (Linked : ∀ x, ∃ y, R x y) : ∀ x, R x x :=
     take x, obtain (w : A) (Hw : R x w), from Linked x,
        let lemma1 : R w x := Symm Hw
        in Trans Hw lemma1

  theorem ReflIf2 (Linked : ∀ x, ∃ y, R x y) : ∀ x, R x x :=
     λ x, exists_elim (Linked x)
            (λ w Hw,
               Trans Hw (Symm Hw))
end

print environment 1
