section
parameters (A : Type) (a b z : A) (add : A → A → A) (le : A → A → Type₀)
local notation 0 := z
local infix + := add
local infix ≤ := le

definition add_zero (x : A) : x + 0 = x := sorry

set_option pp.universes true

definition le_add_of_nonneg_right (H : a + 0 ≤ a + b) : a ≤ a + b :=
begin
  rewrite add_zero at H,
  exact H
end
end
