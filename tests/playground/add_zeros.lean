def add (n m : Nat) : Nat := n + m
@[simp] theorem addZero x : add 0 x = x := by
  simp [add]

syntax "bigAdd0Seq! " num : term

macro_rules
  | `(bigAdd0Seq! $n) =>
    let n := n.toNat
    if n == 0 then
      `(0)
    else
      `(add 0 (bigAdd0Seq! $(Lean.quote (n - 1))))

set_option maxRecDepth 10000

theorem ex : bigAdd0Seq! 20 = 0 := by
  simp

#print ex
