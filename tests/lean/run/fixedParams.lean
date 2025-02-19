set_option trace.Elab.definition.fixedParams true

namespace Ex1

/-- info: [Elab.definition.fixedParams] getFixedParams: [[], []] -/
#guard_msgs(info) in
mutual
def foo : Nat := bar
def bar : Nat := foo
end

end Ex1


namespace Ex2
/--
info: [Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (0)])], [some ([some (0), some (0)])]]
-/
#guard_msgs(info) in
mutual
def foo (n : Nat) : Nat := bar n
def bar (n : Nat) : Nat := foo n
end
end Ex2

namespace Ex3
/--
info: [Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (1)]), some ([some (1), some (0)])],
     [some ([some (1), some (0)]), some ([some (0), some (1)])]]
-/
#guard_msgs(info) in
mutual
def foo (n : Nat) (m : Nat) : Nat := bar m n
def bar (n : Nat) (m : Nat) : Nat := foo m n
end
end Ex3

-- TODO: This should fail, it's not consistent.

namespace Ex4
/--
info: [Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (0)]), some ([some (1), some (1)])],
     [some ([some (1), some (0)]), some ([some (0), some (1)])]]
-/
#guard_msgs(info) in
mutual
def foo (n : Nat) (m : Nat) : Nat := bar m n
def bar (n : Nat) (m : Nat) : Nat := foo n m
end
end Ex4
