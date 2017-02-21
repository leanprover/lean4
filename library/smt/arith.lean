-- TODO(Leo): remove after we port reals to new stdlib
-- Arithmetic
constants (real : Type)

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
