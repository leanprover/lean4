-- constant vector : Type → nat → Type
-- constant vector.nil {α} : vector α 0
-- constant vector.cons {α n} : α → vector α n → vector α (nat.succ n)

-- notation a :: b := vector.cons a b
notation `[` l:(foldr `, ` (h t, vector.cons h t) vector.nil `]`) := l

structure author :=
(name : string)

def f : list author := [{name := "it's a me!"}]
