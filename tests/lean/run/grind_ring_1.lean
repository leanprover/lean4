set_option grind.warning false
open Lean.Grind

example [CommRing α] (x : α) : (x + 1)*(x - 1) = x^2 - 1 := by
  grind +ring

example [CommRing α] [IsCharP α 256] (x : α) : (x + 16)*(x - 16) = x^2 := by
  grind +ring

example (x : Int) : (x + 1)*(x - 1) = x^2 - 1 := by
  grind +ring

example (x : UInt8) : (x + 16)*(x - 16) = x^2 := by
  grind +ring

example (x : Int) : (x + 1)^2 - 1 = x^2 + 2*x := by
  grind +ring

example (x : BitVec 8) : (x + 16)*(x - 16) = x^2 := by
  grind +ring

example (x : BitVec 8) : (x + 1)^2 - 1 = x^2 + 2*x := by
  grind +ring
