set_option old_structure_cmd true

#print prefix semigroup

#print "======================="

class has_two_muls (A : Type) extends has_mul A renaming mul→mul1,
                              private has_mul A renaming mul→mul2

#print prefix has_two_muls

#print "======================="

class another_two_muls (A : Type) extends has_mul A renaming mul→mul1,
                                          has_mul A renaming mul→mul2
