import logic

section
  variables {A : Type}
  variables f : A → A → A
  local infixl `+++`:10 := f

  variables a b c : A
  check f a b
  check a +++ b

  definition foo : nat → bool :=
  λn, bool.tt

  notation `bla`:100 := 10
  local attribute foo [coercion]
  print coercions
end

print coercions -- should be empty
check bla
check 1 +++ 2   -- should say +++ is an invalid expression
open nat
print coercions
