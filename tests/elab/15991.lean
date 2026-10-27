import Lean.Data.Json

/-!
Regression test for #15991: `Float.ofScientific` took time quadratic in the length of the
mantissa when the result overflowed. A JSON number such as `1e100000` reaches it with a long
mantissa, because the parser multiplies the exponent into the mantissa.
-/

/-- info: 9218868437227405312 -/
#guard_msgs in
#eval (Float.ofScientific (10 ^ 100000) false 0).toBits

/-- info: 2139095040 -/
#guard_msgs in
#eval (Float32.ofScientific (10 ^ 100000) false 0).toBits

/-- info: 9218868437227405312 -/
#guard_msgs in
#eval (10 ^ 100000 : Nat).toFloat.toBits

/-- info: 9218868437227405312 -/
#guard_msgs in
#eval match Lean.Json.parse "1e100000" with
  | .ok (.num n) => n.toFloat.toBits
  | _ => 0

/-!
Rounding after a shift by 954 places, where the sticky bit comes from the far end of what is
shifted out. Ties round to even. Each result is `2 ^ 953` or one of the next two floats; the
expected values are the bits of Python's `float` of the same integer.
-/

/-- info: 8899112863684100096 -/
#guard_msgs in
#eval (Float.ofScientific ((2 ^ 53 + 1) * 2 ^ 900) false 0).toBits

/-- info: 8899112863684100098 -/
#guard_msgs in
#eval (Float.ofScientific ((2 ^ 53 + 3) * 2 ^ 900) false 0).toBits

/-- info: 8899112863684100096 -/
#guard_msgs in
#eval (Float.ofScientific (2 ^ 953 + 1) false 0).toBits

/-- info: 8899112863684100097 -/
#guard_msgs in
#eval (Float.ofScientific ((2 ^ 53 + 1) * 2 ^ 900 + 1) false 0).toBits
