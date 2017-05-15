set_option pp.all true

section
parameter α : Type
inductive foo : Type | a : α → foo | b
#check (foo.b : foo)
open foo
#check (foo.b : foo)
#check (b : foo)

open tactic
include α
example : true :=
by do
  e ← to_expr ```(b),
  t ← infer_type e,
  trace "-------",
  trace e,
  trace t,
  trace "-------",
  triv

def ex : foo := begin trace_state, exact b end

end

namespace bla
section
parameter α : Type
inductive foo : Type | a : α → foo | b
#check (foo.b : foo)
open foo
#check (foo.b : foo)
#check (b : foo)
end
end bla

namespace boo
section
parameter α : Type
inductive foo : Type | a : α → foo | b
#check (foo.b : foo)
open foo (b)
#check (foo.b : foo)
#check (b : foo)
end
end boo
