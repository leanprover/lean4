module
@[expose] public section -- TODO: remove after we fix congr_eq
inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

-- The `grind` tactics fail without this `[expose]`
def h (v w : Vec α n) : Nat :=
  match v, w with
  | _, .cons _ (.cons _ _) => 20
  | .nil, _  => 30
  | _, _    => 40

-- In the following example, we need to instruct `grind` to case-split on `Vec` terms because
-- we don't have a propagation rule for given `as : Vec α (n+1)`, then `∃ b bs, as = .cons b bs`
example (a b : Vec α 2) : h a b = 20 := by
  grind [h.eq_def, Vec]

example (a b : Vec α 2) : h a b = 20 := by
  grind (splits := 4) [h.eq_def, Vec]
