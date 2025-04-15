private axiom test_sorry : ∀ {α}, α

set_option trace.Elab.definition.fixedParams true

namespace Ex1

/--
error: well-founded recursion cannot be used, 'Ex1.foo' does not take any (non-fixed) arguments
---
info: [Elab.definition.fixedParams] getFixedParams:
      • ⏎
      •
-/
#guard_msgs in
mutual
def foo : Nat := bar
def bar : Nat := foo
decreasing_by exact test_sorry
end

end Ex1


namespace Ex2
/--
error: well-founded recursion cannot be used, 'Ex2.foo' does not take any (non-fixed) arguments
---
info: [Elab.definition.fixedParams] getFixedParams:
      • [#1 #1]
      • [#1 #1]
-/
#guard_msgs in
mutual
def foo (n : Nat) : Nat := bar n
def bar (n : Nat) : Nat := foo n
decreasing_by exact test_sorry
end
end Ex2

namespace Ex3
/--
error: well-founded recursion cannot be used, 'Ex3.foo' does not take any (non-fixed) arguments
---
info: [Elab.definition.fixedParams] getFixedParams:
      • [#1 #2] [#2 #1]
      • [#2 #1] [#1 #2]
-/
#guard_msgs in
mutual
def foo (n : Nat) (m : Nat) : Nat := bar m n
decreasing_by all_goals exact test_sorry
def bar (n : Nat) (m : Nat) : Nat := foo m n
decreasing_by all_goals exact test_sorry
end
end Ex3

namespace Ex4
/--
info: [Elab.definition.fixedParams] getFixedParams: notFixed 0 3:
    In foo c n b m
    m not matched
[Elab.definition.fixedParams] getFixedParams: • [#1 #3] ❌ [#3 #1] ❌ • [#3 #1] ❌ [#1 #3] ❌
-/
#guard_msgs in
mutual
def foo (a : Nat) (n : Nat) (d : Nat) (m : Nat) : Nat := bar d m a n
decreasing_by exact test_sorry
def bar (b : Nat) (n : Nat) (c : Nat) (m : Nat) : Nat := foo c n b m
decreasing_by exact test_sorry
end
end Ex4

namespace Append1

/--
info: [Elab.definition.fixedParams] getFixedParams: notFixed 0 1:
    In app as bs
    x✝¹ =/= as
[Elab.definition.fixedParams] getFixedParams: notFixed 0 2:
    In app as bs
    x✝ =/= bs
[Elab.definition.fixedParams] getFixedParams: • [#1] ❌ ❌
-/
#guard_msgs(info) in
def app : List α → List α → List α
  | [], bs => bs
  | a::as, bs => a :: app as bs

/--
info: [Elab.definition.fixedParams] getFixedParams: notFixed 0 1:
    In app' as bs
    as✝ =/= as
[Elab.definition.fixedParams] getFixedParams: • [#1] ❌ [#3]
-/
#guard_msgs(info) in
def app' (as : List α) (bs : List α) : List α :=
  match as with
  | [] => bs
  | a::as => a :: app' as bs

end Append1
