open Lean Grind

/-!
Regression test for #16286: `grind` treats a negative literal such as `-1 : Int8` as a literal and
does not internalize the numeral `1` inside it, but `linarith` reified `-1` as the negation of a
variable `1` and failed with "linarith term has not been internalized".
-/

example (x : Int8) (h : -1 ≤ x) : -2 ≤ x := by grind_linarith
example (x : Int16) (h : -1 ≤ x) : -2 ≤ x := by grind_linarith
example (x : Int32) (h : -1 ≤ x) : -2 ≤ x := by grind_linarith
example (x : Int64) (h : -1 ≤ x) : -2 ≤ x := by grind_linarith

/-!
`T` is an ordered `IntModule` but not a `CommRing`, so `linarith` reifies `-1 : T` itself, as the
negation of the variable `1`. Thus, `-1 : T` is not a literal even though `T` reduces to `Int`.
-/

def T := Int
instance : IntModule T := inferInstanceAs (IntModule Int)
instance : LE T := inferInstanceAs (LE Int)
instance : LT T := inferInstanceAs (LT Int)
instance : Std.IsPreorder T := inferInstanceAs (Std.IsPreorder Int)
instance : Std.IsLinearOrder T := inferInstanceAs (Std.IsLinearOrder Int)
instance : Std.LawfulOrderLT T := inferInstanceAs (Std.LawfulOrderLT Int)
instance : OrderedAdd T := inferInstanceAs (OrderedAdd Int)
instance : OfNat T n := inferInstanceAs (OfNat Int n)

example (x y : T) (h₁ : x ≤ -1) (h₂ : y ≤ x) : y ≤ -1 := by grind_linarith
example (x y : T) (h₁ : x ≤ -1) (h₂ : y ≤ x) : y ≤ -1 := by grind

example (x : T) (h : x + 1 ≤ 0) : x ≤ -1 := by grind_linarith
example (x : T) (h : x ≤ -1) : x + 1 ≤ 0 := by grind_linarith
example (x : T) (h : x ≠ -1) (h' : x + 1 = 0) : False := by grind_linarith

example (x y : T) (h₁ : x + 1 ≤ 0) (h₂ : y ≤ x) : y ≤ -1 := by grind
