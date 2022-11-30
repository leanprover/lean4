abbrev M := ExceptT String $ StateT Nat Id

def add (n : Nat) : M Unit :=
  modify (· + 0)

@[simp] theorem add_zero : add (nat_lit 0) = pure () :=
  rfl

syntax "big_add0_seq " num : term

macro_rules
  | `(big_add0_seq $n) =>
    let n := n.toNat
    if n == 0 then
      `(pure ())
    else
      `(add (nat_lit 0) >>= fun _ => big_add0_seq $(Lean.quote (n - 1)))

set_option maxRecDepth 10000

theorem ex : big_add0_seq 10 = pure () := by
  simp

-- set_option pp.explicit true
-- set_option pp.notation false
-- #print ex
