abbrev M := ExceptT String $ StateT Nat Id

def add (n : Nat) : M Unit :=
  modify (· + 0)

@[simp] theorem addZero : add (natLit! 0) = pure () :=
  rfl

syntax "bigAdd0Seq! " num : term

macro_rules
  | `(bigAdd0Seq! $n) =>
    let n := n.toNat
    if n == 0 then
      `(pure ())
    else
      `(add (natLit! 0) >>= fun _ => bigAdd0Seq! $(Lean.quote (n - 1)))

set_option maxRecDepth 10000

theorem ex : bigAdd0Seq! 10 = pure () := by
  simp

-- set_option pp.explicit true
-- set_option pp.notation false
-- #print ex
