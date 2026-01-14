@[elab_as_elim]
def strongSubRecursion {P : Nat → Nat → Sort _} (H : ∀ a b, (∀ x y, x < a → y < b → P x y) → P a b) :
    ∀ n m : Nat, P n m
  | n, m => H n m fun x y _ _ => strongSubRecursion H x y
