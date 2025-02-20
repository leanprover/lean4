set_option trace.Elab.definition.fixedParams true
/-

namespace Ex1

#guard_msgs(info) in
mutual
def foo : Nat := bar
def bar : Nat := foo
end

end Ex1


namespace Ex2
/--
info: [Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (0)])], [some ([some (0), some (0)])]]
[Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (0)])], [some ([some (0), some (0)])]]
-/
#guard_msgs(info) in
mutual
def foo (n : Nat) : Nat := bar n
def bar (n : Nat) : Nat := foo n
end
end Ex2

namespace Ex3
#guard_msgs(info) in
mutual
def foo (n : Nat) (m : Nat) : Nat := bar m n
def bar (n : Nat) (m : Nat) : Nat := foo m n
end
end Ex3

namespace Ex4
#guard_msgs(info) in
mutual
def foo (a : Nat) (n : Nat) (d : Nat) (m : Nat) : Nat := bar d m a n
def bar (b : Nat) (n : Nat) (c : Nat) (m : Nat) : Nat := foo c n b m
end
end Ex4


-/
