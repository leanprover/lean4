/-!
Tests the behavior of string interpolation literals
-/

/-!
Constant values are correctly interpolated.
-/

#eval s!"hello {1+1}"

/-!
Values with variables are correctly interpolated.
-/

def tst (x : Nat) : IO Unit := do
  IO.println s!"x: {x}"
  IO.println s!"x+1: {x+1}"

/--
info: x: 10
x+1: 11
-/
#guard_msgs in
#eval tst 10

/-!
Opening braces (`{`) can be escaped, closing braces (`}`) don't need to be.
-/

/-- info: "{2}" -/
#guard_msgs in
#eval s!"\{{1+1}}"

/-!
String interpolation doesn't add any spaces.
-/

/-- info: "1+1" -/
#guard_msgs in
#eval s!"{1}+{1}"

/-- info: "a1" -/
#guard_msgs in
#eval s!"a{1}"

/-!
String interpolation works correctly with monadic computations.
-/

def g (x : Nat) : StateRefT Nat IO Nat := do
  modify (· + x)
  get

def ex : StateRefT Nat IO Unit := do
  IO.println s!">> hello {← g 1}"
  IO.println s!">> world {← g 1}"

/--
info: >> hello 1
>> world 2
-/
#guard_msgs in
#eval ex.run' 0

/-!
String interpolation elaborates to the individual components wrapped in `toString` and combined
using `++`.
-/

/--
info: toString "he" ++ toString "llo" ++ toString ", " ++ toString "wo" ++ toString "rld" : String
-/
#guard_msgs in
#check s!"he{"llo"}, {"wo"}rld"

/-!
Redundant parts are omitted.
-/

/-- info: toString 1 ++ toString 2 : String -/
#guard_msgs in
#check s!"{1}{2}"
