axiom let_in {A B} (x : A) (f : A -> B) : B
axiom add (x y : Nat) : Nat
@[simp] axiom addZero (x : Nat) : add x 0 = x
syntax "bigAdd0Seq! " num term:max : term
syntax "bigAddSeq! "  num term:max : term

macro_rules
  | `(bigAdd0Seq! $n $acc) =>
    let n := n.toNat
    if n == 0 then
      `(add $acc (add $acc 0))
    else
      `(let_in (add $acc (add $acc 0)) (fun acc' => bigAdd0Seq! $(Lean.quote (n - 1)) acc'))

macro_rules
  | `(bigAddSeq! $n $acc) =>
    let n := n.toNat
    if n == 0 then
      `(add $acc $acc)
    else
      `(let_in (add $acc $acc) (fun acc' => bigAddSeq! $(Lean.quote (n - 1)) acc'))

theorem ex1 (x : Nat) : bigAdd0Seq! 150 x = bigAddSeq! 150 x := by
  simp

-- theorem ex2 (x : Nat) : bigAddSeq! 5 x = bigAddSeq! 5 x := by
--   simp
