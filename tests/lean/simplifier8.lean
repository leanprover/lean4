-- deeper congruence

universe l
constants (T : Type.{l}) (x1 x2 x3 x4 x5 x6 : T) (f : T → T → T)
constants (f_comm : ∀ x y, f x y = f y x)
          (f_l : ∀ x y z, f (f x y) z = f x (f y z))
          (f_r : ∀ x y z, f x (f y z) = f y (f x z))

attribute f_comm [simp]
attribute f_l [simp]
attribute f_r [simp]

#simplify eq 0 (f (f x2 x4) (f x5 (f x3 (f x1 x6))))
