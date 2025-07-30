axiom WellFounded.height [WellFoundedRelation α] : α → Nat

@[simp, grind]
theorem WellFounded.height_nat : WellFounded.height (n : Nat) = n := sorry

variable {α : Type u}
variable [WellFoundedRelation α]

open WellFounded (height)

def Ord.Approx (n : Nat) (i1 i2 : Ord α) : Prop :=
  ∀ x y, height x < n → height y < n → i1.compare x y = i2.compare x y

theorem Ord.Approx.ext (i1 i2 : Ord α) (h : ∀ n, Ord.Approx n i1 i2) : i1 = i2 := by
  ext a b
  apply h (max (height a) (height b) + 1) a b
  · omega
  · omega

def ordNatF (i : Ord Nat) : Ord Nat :=
  { compare x y := match x, y with
    | 0, 0 => Ordering.eq
    | 0, _ => Ordering.lt
    | _, 0 => Ordering.gt
    | n+1, m+1 => i.compare n m
  }

theorem ordNatF_approx (i1 i2 : Ord Nat) (n : Nat)
  (h : ∀ m < n, Ord.Approx m i1 i2) :
  Ord.Approx n (ordNatF i1) (ordNatF i2) := by
  intro x y hx hy
  cases x <;> cases y
  · rfl
  · rfl
  · rfl
  next n m =>
    dsimp [ordNatF]
    apply h (max (height n) (height m) + 1) <;> grind
