set_option grind.warning false
def Matrix (m : Type) (n : Type) (α : Type) : Type :=
  m → n → α

-- Remark: the following test used to fail because `grind` was not using
-- the default reducibility setting when computing the congruence theorem for `M`.

example (o : Type) (m' n' : o → Type) (α : Type)
    (M : (i : o) → Matrix (m' i) (n' i) α)
    (ii : o) (ix : n' ii) (ji : o) (jx : m' ji)
    (j : ii = ji) :
    M ji jx (cast (congrArg n' j) ix) = M ii (cast (congrArg m' j.symm) jx) ix := by
  grind
