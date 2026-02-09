import Lean
/-!
# Tests for delaboration of constants (and name unresolution)
-/

set_option linter.unusedVariables false

/-!
Make sure unresolution avoids conflicts.
-/
def A.B.x : Nat := 0
def A.B'.x : Nat := 0

/-- info: x : Nat -/
#guard_msgs in open A B in #check (A.B.x)
/-- info: B'.x : Nat -/
#guard_msgs in open A B in #check (A.B'.x)
/-- info: B.x : Nat -/
#guard_msgs in open A B B' in #check (A.B.x)
/-- info: B'.x : Nat -/
#guard_msgs in open A B B' in #check (A.B'.x)

/-!
Another conflict check.
-/
def B.x : Nat := 0
/-- info: A.B.x : Nat -/
#guard_msgs in open A in #check (A.B.x)
-- Resolution accepts this exact match.
/-- info: B.x : Nat -/
#guard_msgs in open A in #check (B.x)

/-!
Opening does not shadow the `x` that's already in `B`.
-/
namespace B
open A.B
/-- info: A.B.x : Nat -/
#guard_msgs in #check (_root_.A.B.x)
/-- info: x : Nat -/
#guard_msgs in #check (_root_.B.x)
/-- info: x : Nat -/
#guard_msgs in #check (x)
end B

/--
A global `x` needs the `_root_` qualifier.
-/
def x : Nat := 0
namespace B
/-- info: _root_.x : Nat -/
#guard_msgs in #check (_root_.x)
/-- info: x : Nat -/
#guard_msgs in #check (B.x)
end B

/-!
Name that shadows a local constant needs `_root_`.
-/
/--
trace: id : Nat
⊢ _root_.id 2 = 2
-/
#guard_msgs in
example (id : Nat) : _root_.id 2 = 2 := by
  trace_state
  rfl

/-!
Even with `id.{1}` notation, the name `id` must not shadow the local constant.
-/
/--
trace: id : Nat
⊢ Eq.{1} (_root_.id.{1} 2) 2
-/
#guard_msgs in
set_option pp.universes true in
example (id : Nat) : _root_.id 2 = 2 := by
  trace_state
  rfl

/-!
In `pp.fullNames` mode, local name shadowing is still checked.
-/
/--
trace: id : Nat
⊢ _root_.id 2 = 2
-/
#guard_msgs in
set_option pp.fullNames true in
example (id : Nat) : _root_.id 2 = 2 := by
  trace_state
  rfl
/-- info: `_root_.id -/
#guard_msgs in
variable (id : Nat) in
#eval Lean.Elab.Command.runTermElabM fun _ =>
  Lean.unresolveNameGlobalAvoidingLocals ``id (fullNames := true)

/-!
`match` shadowing test. This used to print the first `match` arm as
`| Bool.true => 0`, which is incorrect, since `Bool.true` resolves to `MatchTest1.Bool.true`
-/
namespace MatchTest1

def Bool.true := 0
set_option linter.constructorNameAsVariable false in
def f (true : Bool) : Nat :=
  match true with
  | _root_.Bool.true => 0
  | false => 1

/--
info: def MatchTest1.f : Bool → Nat :=
fun true =>
  match true with
  | _root_.Bool.true => 0
  | false => 1
-/
#guard_msgs in
#print f

/-- info: Bool.true : Nat -/
#guard_msgs in #check (Bool.true)

end MatchTest1

/-!
`match` shadowing test. This used to print the first `match` arm as
`| Bool.true => 0`, which is incorrect, since `Bool.true` resolves to the local variable.
-/
namespace MatchTest2

set_option linter.constructorNameAsVariable false in
def f (true : Bool) : Nat :=
  let Bool.true := 1
  match true with
  | _root_.Bool.true => 0
  | false => 1

/--
info: def MatchTest2.f : Bool → Nat :=
fun true =>
  have Bool.true := 1;
  match true with
  | _root_.Bool.true => 0
  | false => 1
-/
#guard_msgs in
#print f

end MatchTest2

/-!
`match` shadowing test. Similar to `MatchTest2`, but `| Bool.false =>` is correct.
-/
namespace MatchTest3

set_option linter.constructorNameAsVariable false in
def f (true : Bool) :=
  let Bool.true := true
  let false := true
  match true with
  | _root_.Bool.true => false
  | Bool.false =>
    match true with
    | Bool.false => false
    | false => Bool.true
/--
info: def MatchTest3.f : Bool → Bool :=
fun true =>
  have Bool.true := true;
  have false := true;
  match true with
  | _root_.Bool.true => false
  | Bool.false =>
    match true with
    | Bool.false => false
    | false => Bool.true
-/
#guard_msgs in open Bool in #print f

end MatchTest3

namespace PrvTest.NS1

private abbrev fst : Nat × Nat → Nat := fun s => s.1
private abbrev snd : Nat × Nat → Nat := fun s => s.2

/-!
The private names get unresolved. Previously this would print as
`PrvTest.NS1.fst (x, x) = PrvTest.NS1.snd (x, x)`.
-/
/--
trace: x : Nat
⊢ fst (x, x) = snd (x, x)
-/
#guard_msgs in
example (x : Nat) : fst (x,x) = snd (x,x) := by
  trace_state
  rfl

end NS1

export NS1 (fst)

/-!
Private names get unresolved with respect to the namespace, and aliases are respected too.
-/
/--
trace: x : Nat
⊢ fst (x, x) = NS1.snd (x, x)
-/
#guard_msgs in
example (x : Nat) : fst (x,x) = NS1.snd (x,x) := by
  trace_state
  rfl

end PrvTest

/-!
The name `IO.CancelToken.ref✝` is a private imported name.
-/
/--
info: def IO.CancelToken.isSet : IO.CancelToken → BaseIO Bool :=
fun tk => ST.Ref.get (IO.CancelToken.ref✝ tk)
-/
#guard_msgs in #print IO.CancelToken.isSet
/-!
Even if `IO` is opened, it won't print as `CancelToken.ref✝`, but the full name.
-/
/--
info: def IO.CancelToken.isSet : CancelToken → BaseIO Bool :=
fun tk => ST.Ref.get (IO.CancelToken.ref✝ tk)
-/
#guard_msgs in open IO in #print IO.CancelToken.isSet
