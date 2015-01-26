import logic

section
  variables {A : Type}
  variables f : A → A → A
  local infixl `+++`:10 := f

  variables a b c : A
  check f a b
  check a +++ b
end
