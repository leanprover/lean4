inductive Nested
| nest (a : Array Nested) : Nested

class OfUnit (α : Type) where
  ofUnit : Unit → Except String α

instance myArrayInst [OfUnit α] : OfUnit (Array α) where
  ofUnit _ := Except.error ""
open OfUnit

partial def ofUnitNested (_ : Unit) : Except String Nested := do
  let localinst : OfUnit Nested := ⟨ofUnitNested⟩
  let units : Array Unit ← Except.ok #[]
  let a ← ofUnit ()
  return Nested.nest a
