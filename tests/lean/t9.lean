prelude precedence `+` : 65
precedence `*` : 75
precedence `=` : 50
precedence `≃` : 50
constant N : Type.{1}
constant a : N
constant b : N
constant add : N → N → N
constant mul : N → N → N
namespace foo
  infixl + := add
  infixl * := mul
  check a+b*a
end foo
-- Notation is not avaiable outside the namespace
check a+b*a
namespace foo
  -- Notation is restored
  check a+b*a
end foo
