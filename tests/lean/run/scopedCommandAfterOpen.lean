namespace Internal
scoped macro "foo" : command => `(#print "foo")
end Internal

section
open Internal
foo
end
