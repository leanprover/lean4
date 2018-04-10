set_option trace.inductive_compiler.nested.define.failure true
set_option max_memory 1000000

inductive {u} vec (A : Type u) : nat -> Type u
| vnil : vec 0
| vcons : Pi (n : nat), A -> vec n -> vec (n+1)

namespace X6
#print "locals + nested-reflexive locals in indices"
inductive {u} foo (A : Type u) : Type u
| mk : Pi (n : nat), A -> (Pi (m : nat), vec foo (n + m)) -> foo

#check foo.sizeof
#check foo.mk.sizeof_spec

end X6

namespace X8
#print "many different nestings, some sharing"
inductive {u} foo (A : Type u) : Type u
| mk₁ : Pi (n : nat), A -> (Pi (m : nat), vec (list foo) (n + m)) -> vec foo n -> foo
| mk₂ : Pi (n : nat), A -> list A -> prod A A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo

#check foo.sizeof
#check foo.mk₁.sizeof_spec
#check foo.mk₂.sizeof_spec

end X8

namespace X9b
#print "mutual + nesting"
mutual inductive {u} foo, bar
with foo : Type u
| mk : list (list foo) -> foo
with bar : Type u
| mk : list foo -> bar

#check foo.sizeof
#check foo.mk.sizeof_spec
#check bar.sizeof
#check bar.mk.sizeof_spec

end X9b

namespace X11
#print "intro rule that introduces additional nesting"

inductive {u} wrap (A : Type u) : Type u
| mk : list A -> wrap

inductive {u} foo : Type u
| mk : wrap foo -> foo

#check foo.sizeof
#check foo.mk.sizeof_spec

end X11
