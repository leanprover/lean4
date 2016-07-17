open tactic
constants (A : Type.{1})
constants (op : A → A → A) (op.comm : ∀ x y, op x y = op y x) (op.assoc : ∀ x y z, op (op x y) z = op x (op y z)) (op.left_comm : ∀ x y z, op x (op y z) = op y (op x z))
attribute op.comm [simp]
attribute op.assoc [simp]
attribute op.left_comm [simp]
set_option simplify.max_steps 1000000
constants (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 : A)
example : (op x1 (op x2 (op x3 (op x4 (op x5 (op x6 (op x7 (op x8 (op x9 (op x10 (op x11 (op x12 (op x13 (op x14 (op x15 (op x16 (op x17 (op x18 (op x19 (op x20 (op x21 (op x22 (op x23 (op x24 (op x25 (op x26 (op x27 (op x28 (op x29 (op x30 (op x31 (op x32 (op x33 (op x34 (op x35 (op x36 (op x37 (op x38 (op x39 (op x40 (op x41 (op x42 (op x43 (op x44 (op x45 (op x46 (op x47 (op x48 (op x49 (op x50 x0)))))))))))))))))))))))))))))))))))))))))))))))))) = (op x50 (op x49 (op x48 (op x47 (op x46 (op x45 (op x44 (op x43 (op x42 (op x41 (op x40 (op x39 (op x38 (op x37 (op x36 (op x35 (op x34 (op x33 (op x32 (op x31 (op x30 (op x29 (op x28 (op x27 (op x26 (op x25 (op x24 (op x23 (op x22 (op x21 (op x20 (op x19 (op x18 (op x17 (op x16 (op x15 (op x14 (op x13 (op x12 (op x11 (op x10 (op x9 (op x8 (op x7 (op x6 (op x5 (op x4 (op x3 (op x2 (op x1 x0)))))))))))))))))))))))))))))))))))))))))))))))))) := by simp
