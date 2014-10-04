import logic

section
  variables (A B C : Type)
  definition foo := A → B

  check foo A B
  check foo B C
  check foo A A
end

constants A B C : Type
check foo A B
check foo B C
check foo A A

section
  variables (A B C : Type)
  definition foo2 := A → B

  check foo2 A B
  check foo2 B C
  check foo2 A A
end
