constant vector : Type → nat → Type
constant vector.nil {α} : vector α 0
constant vector.cons {α n} : α → vector α n → vector α (nat.succ n)

notation a :: b := vector.cons a b
notation `[` l:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := l

example (u : vector ℕ 2) : vector ℕ 2 :=
let [u1, u2] := u in
u
