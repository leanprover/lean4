constant f : ℕ → ℕ
axiom foo {m n : ℕ} : f m = m

attribute [ematch] foo

example : true := begin[smt] eblast end
