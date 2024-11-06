/-!
# `partial` inhabitation with delta derivation
-/
set_option pp.mvars false

/-!
In the following, `partial` needs to unfold the return type to find an Inhabited instance.
-/
def MyGreatType (α : Type) := α × α

partial def myLessGreatFunction (n : Nat) : MyGreatType Nat := myLessGreatFunction n


/-!
In the following, it needs to unfold underneath a forall.
-/
def MyGreaterType (α : Type) := α → MyGreatType α

partial def myEvenLessGreatFunction (n : Nat) : MyGreaterType Nat := myEvenLessGreatFunction n


/-!
Regression test: can use existing parameter.
-/
partial def test1 (x : α) : α := test1 x

/-!
Regression test: can use Inhabited instance in parameter list.
-/
partial def test2 [Inhabited α] (n : Nat) : α := test2 n

/-!
Regression test: can use Nonempty instance in parameter list.
-/
partial def test3 [Nonempty α] (n : Nat) : α := test3 n

/-!
Error message.
-/
/--
error: failed to compile 'partial' definition 'test4', could not prove that the type
  {α : Sort u_1} → Nat → α
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in partial def test4 (n : Nat) : α := test4 n

/-!
Add arguments as inhabited instances.
Example adapted from https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Why.20return.20type.20of.20partial.20function.20MUST.20.60inhabited.60.3F/near/477905312
-/
inductive ListNode where
  | mk : Nat → Option ListNode → ListNode

partial def checkMyList (head : ListNode) : Bool × ListNode := checkMyList head
