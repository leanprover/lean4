/-!
# Encode (some) optional parameters in the structure constructor
-/

/-
Example in issue #4736.
The `another_value` field was not an optParam in the constructor.
-/

structure NonEmptyString where
  value : String
  another_value : Int := 0
  ev : value.length > 0 := by decide

example : NonEmptyString := NonEmptyString.mk "hello"

-- However, users are intended to use structure instance notation.
example : NonEmptyString := { value := "hello" }
