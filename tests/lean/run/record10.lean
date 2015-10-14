import logic

structure semigroup [class] (A : Type) extends has_mul A :=
(assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

print prefix semigroup

print "======================="

structure has_two_muls [class] (A : Type) extends has_mul A renaming mul→mul1,
                                          private has_mul A renaming mul→mul2

print prefix has_two_muls

print "======================="

structure another_two_muls [class] (A : Type) extends has_mul A renaming mul→mul1,
                                                      has_mul A renaming mul→mul2
