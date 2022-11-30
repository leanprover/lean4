def add (n m : Nat) : Nat := n + m
@[simp] theorem add_zero x : add 0 x = x := by
  simp [add]

syntax "big_add0_seq " num : term

macro_rules
  | `(big_add0_seq $n) =>
    let n := n.toNat
    if n == 0 then
      `(0)
    else
      `(add 0 (big_add0_seq $(Lean.quote (n - 1))))

set_option maxRecDepth 10000

theorem ex : big_add0_seq 20 = 0 := by
  simp

#print ex
