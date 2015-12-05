definition f (a : nat) := a + 1

attribute f [reducible] at foo

print f

section
  open foo
  print f
end

print f

namespace foo
  print f
end foo
