opaque fin_max {n: Nat} (f: Fin n → Nat) : Nat

set_option maxRecDepth 30 in
-- NB: Important to not specify the implicit argument of fin_max here
def test (a: Array Nat) : Nat := @fin_max _ fun i =>
  let h : i < a.size := by
    -- this may apply once
    with_reducible apply Fin.val_lt_of_le
    fail_if_success with_reducible apply Fin.val_lt_of_le;
    exact Nat.le_refl _
  a[i]

set_option pp.mvars false

-- This used to cause
-- error: maximum recursion depth has been reached in #5061

/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
a : Array Nat
i : Fin ?_
⊢ ↑i < a.size
-/
#guard_msgs in
set_option maxRecDepth 40 in
def test2 (a: Array Nat) : Nat := @fin_max _ fun i =>
  let h : i < a.size := by
    get_elem_tactic
  a[i]
