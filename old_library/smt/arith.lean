import algebra.ordered_field

-- Arithmetic
constants (int real : Type.{1})
constants (int_has_zero : has_zero int)
constants (int_has_one : has_one int)
constants (int_has_add : has_add int)
constants (int_has_mul : has_mul int)
constants (int_has_sub : has_sub int)
constants (int_has_neg : has_neg int)
constants (int_has_div : has_div int)
constants (int_has_lt : has_lt int)
constants (int_has_le : has_le int)
constants (int_has_mod : has_mod int)
constants (int_decidable_linear_ordered_comm_group : decidable_linear_ordered_comm_group int)
attribute [instance] int_has_zero int_has_one int_has_add int_has_mul int_has_sub int_has_div int_has_neg int_has_le int_has_lt int_has_mod int_decidable_linear_ordered_comm_group

constants (real_has_zero : has_zero real)
constants (real_has_one : has_one real)
constants (real_has_add : has_add real)
constants (real_has_mul : has_mul real)
constants (real_has_sub : has_sub real)
constants (real_has_neg : has_neg real)
constants (real_has_div : has_div real)
constants (real_has_lt : has_lt real)
constants (real_has_le : has_le real)

attribute [instance] real_has_zero real_has_one real_has_add real_has_mul real_has_sub real_has_neg real_has_div real_has_le real_has_lt

constants (real.of_int : int → real) (real.to_int : real → int) (real.is_int : real → Prop)
