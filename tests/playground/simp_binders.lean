axiom let_in {A B} (x : A) (f : A -> B) : B
axiom add (x y : Nat) : Nat
@[simp] axiom addZero (x : Nat) : add x 0 = x
syntax "big_add0_seq " num term:max : term
syntax "big_add_seq "  num term:max : term

macro_rules
  | `(big_add0_seq $n $acc) =>
    let n := n.toNat
    if n == 0 then
      `(add $acc (add $acc 0))
    else
      `(let_in (add $acc (add $acc 0)) (fun acc' => big_add0_seq $(Lean.quote (n - 1)) acc'))

macro_rules
  | `(big_add_seq $n $acc) =>
    let n := n.toNat
    if n == 0 then
      `(add $acc $acc)
    else
      `(let_in (add $acc $acc) (fun acc' => big_add_seq $(Lean.quote (n - 1)) acc'))

theorem ex1 (x : Nat) : big_add0_seq 150 x = big_add_seq 150 x := by
  simp

-- theorem ex2 (x : Nat) : big_add_seq 5 x = big_add_seq 5 x := by
--   simp
