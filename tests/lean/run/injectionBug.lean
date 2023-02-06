inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
  deriving DecidableEq

inductive Test (α : Type)
  | mk (n : Nat) (xs : Vec α n)

def test [DecidableEq α] (x y : Test α) : Decidable (x = y) :=
  match x, y with
  | Test.mk n xs, Test.mk m ys =>
    if h : n = m then by
      subst h
      exact if h : xs = ys then by
        subst h; exact isTrue rfl
      else by
        apply isFalse; intro n; injection n; apply h _; assumption; done
    else by
      apply isFalse; intro n; injection n; apply h _; assumption; done
