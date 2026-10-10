/-!
# Test variable inclusion for `axiom`
-/

/-!
Unused variables (here `unit`) are not included into `axiom`s even if some binders contain
synthetic metavariables (here the index proof for `as[i]`).
-/

variable {α : Type u} {unit : α}

axiom unit_yes {as : Array α} (h : ∀ i, (hi : i < as.size) → as[i] = as[i]) : True

/--
info: axiom unit_yes.{u} : ∀ {α : Type u} {as : Array α}, (∀ (i : Nat) (hi : i < as.size), as[i] = as[i]) → True
-/
#guard_msgs in
#print unit_yes
