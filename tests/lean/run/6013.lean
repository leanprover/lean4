
/--
error: failed to synthesize
  OfNat (String → String) 10
numerals are polymorphic in Lean, but the numeral `10` cannot be used in a context where the expected type is
  String → String
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (a : String) : String :=
  let x : String → String := _
  have : x = 10 := by rfl
  "tested"




structure A where
  α : Type
  a : α

structure B (f : (α : Type) → α → α) extends A where
  b : α
  a := f α b

/--
error: don't know how to synthesize placeholder
context:
⊢ { α := Nat, a := id ?_ }.α
-/
#guard_msgs in
example : B @id where
  α := Nat
  b := _




class One (α : Type) where
  one : α

variable (R A : Type) [One R] [One A]

class OneHom where
  toFun : R → A
  map_one : toFun One.one = One.one

structure Subone where
  mem : R → Prop
  one_mem : mem One.one

structure Subalgebra [OneHom R A] extends Subone A : Type where
  algebraMap_mem : ∀ r : R, mem (OneHom.toFun r)
  one_mem := OneHom.map_one (R := R) (A := A) ▸ algebraMap_mem One.one

/--
error: don't know how to synthesize placeholder
context:
R A : Type
inst✝² : One R
inst✝¹ : One A
inst✝ : OneHom R A
⊢ ∀ (r : R), { mem := ?_ R A _example, one_mem := ⋯ }.mem (OneHom.toFun r)
---
error: don't know how to synthesize placeholder
context:
R A : Type
inst✝² : One R
inst✝¹ : One A
inst✝ : OneHom R A
⊢ A → Prop
-/
#guard_msgs in
example [OneHom R A] : Subalgebra R A where
  mem := _
  algebraMap_mem := _
