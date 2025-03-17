/-!
The elaboration pre-check of `variable`s should not fail on mixed binder updates (nor on shadowing)
-/

variable (α : Type _) [OfNat α (nat_lit 0)]
variable {α} (x : α) (h : x = 0)

variable (α : Type _) [OfNat α (nat_lit 0)]
variable {α} (x : α)
variable (h : x = 0)

variable (α : Type _) [OfNat α (nat_lit 0)]
variable {α}
variable (x : α) (h : x = 0)
