structure [class] semigroup (A : Type) extends has_mul A :=
(assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

print prefix semigroup

print "======================="

structure [class] has_two_muls (A : Type) extends has_mul A renaming mul→mul1,
                                          private has_mul A renaming mul→mul2

print prefix has_two_muls

print "======================="

structure [class] another_two_muls (A : Type) extends has_mul A renaming mul→mul1,
                                                      has_mul A renaming mul→mul2
