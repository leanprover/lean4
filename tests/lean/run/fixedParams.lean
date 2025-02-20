set_option trace.Elab.definition.fixedParams true

namespace Ex1

#guard_msgs(drop all) in
/-- info: [Elab.definition.fixedParams] getFixedParams: [[], []] -/
#guard_msgs(info) in
mutual
def foo : Nat := bar
def bar : Nat := foo
decreasing_by decreasing_tactic
end

end Ex1


namespace Ex2
#guard_msgs(drop all) in
/--
info: [Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (0)])], [some ([some (0), some (0)])]]
-/
#guard_msgs(info) in
mutual
def foo (n : Nat) : Nat := bar n
def bar (n : Nat) : Nat := foo n
decreasing_by decreasing_tactic
end
end Ex2

namespace Ex3
#guard_msgs(drop all) in
/--
info: [Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (1)]), some ([some (1), some (0)])],
     [some ([some (1), some (0)]), some ([some (0), some (1)])]]
-/
#guard_msgs(info) in
mutual
def foo (n : Nat) (m : Nat) : Nat := bar m n
def bar (n : Nat) (m : Nat) : Nat := foo m n
decreasing_by decreasing_tactic
end
end Ex3

namespace Ex4
#guard_msgs(drop all) in
/--
info: [Elab.definition.fixedParams] getFixedParams: [[some ([some (0), some (2)]), none, some ([some (2), some (0)]), none],
     [some ([some (2), some (0)]), none, some ([some (0), some (2)]), none]]
-/
#guard_msgs(info) in
mutual
def foo (a : Nat) (n : Nat) (d : Nat) (m : Nat) : Nat := bar d m a n
def bar (b : Nat) (n : Nat) (c : Nat) (m : Nat) : Nat := foo c n b m
decreasing_by decreasing_tactic
end
end Ex4
