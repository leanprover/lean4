open List
reset_grind_attrs%
set_option grind.warning false

--- Failing with:
--- [issue] unexpected metavariable during internalization
---       ?α
---     `grind` is not supposed to be used in goals containing metavariables.
-- [issue] type error constructing proof for Array.eq_empty_of_append_eq_empty
--     when assigning metavariable ?xs with
--       l₁
--     has type
--       List α : Type u_1
--     but is expected to have type
--       Array ?α : Type ?u.430
theorem dropLast_concat' : dropLast (l₁ ++ [b]) = l₁ := by
   set_option trace.Meta.debug true in
   grind (gen := 6) [→ Array.eq_empty_of_append_eq_empty, Vector.getElem?_append, eq_nil_of_length_eq_zero, getElem?_dropLast]
