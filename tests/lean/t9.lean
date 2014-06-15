precedence `+` : 65
precedence `*` : 75
precedence `=` : 50
precedence `≃` : 50
variable N : Type.{1}
variable a : N
variable b : N
variable add : N → N → N
variable mul : N → N → N
namespace foo
  infixl + : add
  infixl * : mul
  check a+b*a
end
-- Notation is not avaiable outside the namespace
check a+b*a
namespace foo
  -- Notation is restored
  check a+b*a
end
