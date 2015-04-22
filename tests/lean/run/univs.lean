import algebra.category.basic

set_option pp.universes true
section
  universes l₁ l₂ l₃ l₄
  parameter C : Category.{l₁ l₂}
  parameter f : Category.{l₁ l₂} → Category.{l₃ l₄}
  check f C
end
