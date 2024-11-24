/-! Test `·` being able to refer to constants in `simp` -/

example : ¬ true = false := by
  simp [(¬ ·)]

/-! Test `binop%` -/

/--
info: y x : Nat
h : y = 0
⊢ Add.add x y = x
-/
#guard_msgs in
example (h : y = 0) : x + y = x := by
  simp [(.+.)] -- Expands `HAdd.hAdd
  trace_state
  simp [Add.add]
  simp [h, Nat.add]
  done

/--
info: y x : Nat
h : y = 0
⊢ Add.add x y = x
-/
#guard_msgs in
example (h : y = 0) : x + y = x := by
  simp [.+.]
  trace_state
  simp [Add.add]
  simp [h, Nat.add]
  done

/-! Test `binop%` variant `rightact%` as well -/

/--
error: unsolved goals
x y : Nat
⊢ Pow.pow x y = Pow.pow y x
-/
#guard_msgs in
example (x y : Nat) : x ^ y = y ^ x := by
  simp only [.^.]


def f (n m : Nat) : Nat := n + m
macro "ff" t1:term:arg t2:term:arg : term => `(f $t2 $t1)

/--
error: unsolved goals
x y : Nat
⊢ [x + y, y + x].sum > 0
-/
#guard_msgs in
example (x y : Nat) : [f x y, ff x y].sum > 0  := by
  simp only [ff · ·] -- NB: ff is syntax, this unfolds also f


/--
error: unsolved goals
x y : Nat
⊢ List.Mem x [x]
-/
#guard_msgs in
example (x y : Nat) : x ∈ [x] := by
  simp only [· ∈ ·] -- syntax has arguments swapped, see #5905
