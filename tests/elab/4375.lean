example: Nat → Nat :=
  let a : Nat := Nat.zero
  fun (_ : Nat) =>
    let b : Nat := Nat.zero
    (fun (_ : a = b) => 0) (Eq.refl a)
