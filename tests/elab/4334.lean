/-!
# Fix for issue #4334

Non-terminal "partial" `calc` could erroneously fail if there was mdata in the type.
-/

/-!
Worked before.
-/
/--
error: unsolved goals
case calc.step
x y : Nat
⊢ 8 ≤ 10
-/
#guard_msgs in
example {x y : Nat} : x + y ≤ 10 := by
  calc x + y ≤ 7 := sorry
    _ = 8 := sorry
  done

/-!
Worked after adding a `consumeMData`.
-/
/--
error: unsolved goals
case calc.step
x y : Nat
hk : x + y = 4
⊢ 8 ≤ 10
-/
#guard_msgs in
example {x y : Nat} : x + y ≤ 10 := by
  have hk : x + y = 4 := sorry
  calc x + y ≤ 7 := sorry
    _ = 8 := sorry
  done

/-!
Worked after adding an `instantiateMVars` for the proof type after elaborating `calc`.
-/
/--
error: unsolved goals
case calc.step
x y : Nat
hk : x + y ≤ 7
⊢ 8 ≤ 10
-/
#guard_msgs in
example {x y : Nat} : x + y ≤ 10 := by
  have hk : ?a := ?b
  case b =>
    exact (sorry : x + y ≤ 7)
  calc
    x + y ≤ 7 := hk
    _ = 8 := sorry
  done
