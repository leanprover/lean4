@[simp] def take [S : Stream ρ τ] (s : ρ) : Nat → List τ × ρ
| 0 => ([], s)
| n+1 =>
  match S.next? s with
  | none => ([], s)
  | some (x,rest) =>
    let (L,rest) := take rest n
    (x::L, rest)
