import macros

scope
   theorem ReflIf (A : Type)
                  (R : A → A → Bool)
                  (Symm : ∀ x y, R x y → R y x)
                  (Trans : ∀ x y z, R x y → R y z → R x z)
                  (Linked : ∀ x, ∃ y, R x y)
                  :
                  ∀ x, R x x :=
       λ x, obtain (w : A) (H : R x w), from (Linked x),
            let L1 : R w x := Symm x w H
            in Trans x w x H L1

pop::scope

scope
  -- Same example again.
  variable A : Type
  variable R : A → A → Bool
  axiom Symm  {x y : A} : R x y → R y x
  axiom Trans {x y z : A} : R x y → R y z → R x z
  axiom Linked (x : A) : ∃ y, R x y

  theorem ReflIf (x : A) : R x x :=
      obtain (w : A) (H : R x w), from (Linked x),
      let L1 : R w x := Symm H
      in Trans H L1

end

-- Display the last two theorems
print environment 2