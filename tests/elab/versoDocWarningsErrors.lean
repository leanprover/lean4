import Lean

set_option doc.verso true

/-!
This test checks that suggestions for error/warnings flags are provided correctly by the {lit}`lean`
code block in Verso docstrings, and that the messages are saved correctly.
-/


/--
error: Unexpected warning:
  declaration uses `sorry`

Hint: The `+warning` flag indicates that warnings are expected:
  lean ̲+̲w̲a̲r̲n̲i̲n̲g̲
-/
#guard_msgs in
/-!
```lean
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := sorry
```
-/

/--
error: Unexpected warning:
  declaration uses `sorry`

Hint: The `+warning` flag indicates that warnings are expected:
  lean ̲+̲w̲a̲r̲n̲i̲n̲g̲
-/
#guard_msgs in
/-!
```lean
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := sorry
```
-/

-- Also test that adding +warning makes the warning expected (no error)
#guard_msgs in
/-!
```lean +warning
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := sorry
```
-/

-- And that the output is saved
#guard_msgs in
/-!
```lean +warning (name := w)
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := sorry
```
```output w
declaration uses `sorry`
```
-/

/--
error: Unexpected error:
  Type mismatch
    True.intro
  has type
    True
  but is expected to have type
    ∃ n, Int.ofNat n = z

Hint: The `+error` flag indicates that errors are expected:
  lean ̲+̲e̲r̲r̲o̲r̲
-/
#guard_msgs in
/-!
```lean
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := True.intro
```
-/

-- Also test that adding +error makes the error expected (no error)
#guard_msgs in
/-!
```lean +error
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := True.intro
```
-/

-- And that the output is saved
#guard_msgs in
/-!
```lean +error (name := w)
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := True.intro
```
```output w
Type mismatch
  True.intro
has type
  True
but is expected to have type
  ∃ n, Int.ofNat n = z
```
-/
