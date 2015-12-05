namespace foo
namespace bah
namespace bla
section
section
section

definition f (a : nat) := a + 1
attribute f [reducible] at foo.bah
definition g (a : nat) := a + a
attribute g [reducible] at _root_

print "sec 3. " print f print g
end
print "sec 2. " print f print g
end
print "sec 1. " print f print g
end
print "foo.bah.bla. " print f print g
end bla

print "foo.bah. " print foo.bah.bla.f print foo.bah.bla.g
end bah
print "foo. " print foo.bah.bla.f print foo.bah.bla.g
end foo
print "root. " print foo.bah.bla.f print foo.bah.bla.g
