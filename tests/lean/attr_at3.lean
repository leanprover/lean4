namespace bla
definition f (a : nat) := a + 1
attribute f [reducible] at foo
print f
end bla


section
  open foo
  print bla.f
end

print bla.f

namespace foo
  print bla.f
end foo
