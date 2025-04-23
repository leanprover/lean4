reset_grind_attrs%

open List

attribute [grind →] Array.eq_empty_of_append_eq_empty

-- [issue] unexpected metavariable during internalization
--       ?α
--     `grind` is not supposed to be used in goals containing metavariables.
theorem dropLast_concat : dropLast (l₁ ++ [b]) = l₁ := by grind
