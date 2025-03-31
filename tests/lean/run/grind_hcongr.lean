def Matrix (m : Type) (n : Type) (α : Type) : Type :=
  m → n → α

example (o : Type) (m' n' : o → Type) (α : Type)
    (M : (i : o) → Matrix (m' i) (n' i) α)
    (ii : o) (ix : n' ii) (ji : o) (jx : m' ji)
    (j : ii = ji) :
    M ji jx (cast sorry ix) = M ii (cast sorry jx) ix := by
  grind -- fails with "failed to generate hcongr theorem, insufficient number of arguments"
