open function

instance decidable_uncurry_pred{α} (p : α → α → Prop) [decidable_rel p] : decidable_pred (uncurry p) :=
λ a, by { cases a; simp [uncurry]; apply_instance }
