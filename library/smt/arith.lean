constants (real : Type)

constants (real.has_zero : has_zero real)
constants (real.has_one : has_one real)
constants (real.has_add : has_add real)
constants (real.has_mul : has_mul real)
constants (real.has_sub : has_sub real)
constants (real.has_neg : has_neg real)
constants (real.has_div : has_div real)
constants (real.has_lt : has_lt real)
constants (real.has_le : has_le real)

attribute [instance] real.has_zero real.has_one real.has_add real.has_mul real.has_sub real.has_neg real.has_div real.has_le real.has_lt

constants (real.of_int : int → real) (real.to_int : real → int) (real.is_int : real → Prop)
