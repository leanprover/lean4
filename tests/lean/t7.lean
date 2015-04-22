prelude definition Prop : Type.{1} := Type.{0}
constant and : Prop → Prop → Prop
section
  parameter {A : Type}  -- Mark A as implicit parameter
  parameter   R : A → A → Prop
  parameter   B : Type
  definition  id (a : A) : A := a
  private definition  refl : Prop := ∀ (a : A), R a a
  definition  symm : Prop := ∀ (a b : A), R a b → R b a
  definition  trans : Prop := ∀ (a b c : A), R a b → R b c → R a c
  definition  equivalence : Prop := and (and refl symm) trans
end
check id.{2}
check trans.{1}
check symm.{1}
check equivalence.{1}
(*
local env = get_env()
print(env:find("equivalence"):value())
*)
