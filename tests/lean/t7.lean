variable and : Bool → Bool → Bool
section
  {parameter} A : Type  -- Mark A as implicit parameter
  parameter   R : A → A → Bool
  parameter   B : Type
  definition  id (a : A) : A := a
  definition [private] refl : Bool := ∀ (a : A), R a a
  definition  symm : Bool := ∀ (a b : A), R a b → R b a
  definition  trans : Bool := ∀ (a b c : A), R a b → R b c → R a c
  definition  equivalence : Bool := and (and refl symm) trans
end
check id.{2}
check trans.{1}
check symm.{1}
check equivalence.{1}
(*
local env = get_env()
print(env:find("equivalence"):value())
*)
