import Lean
/-!
# Tests for structure resolution order.

https://github.com/leanprover/lean4/issues/3467
https://github.com/leanprover/lean4/issues/1881
-/

/-!
Basic diamond
-/

set_option structure.strictResolutionOrder true
set_option trace.Elab.structure.resolutionOrder true

/-- info: [Elab.structure.resolutionOrder] computed resolution order: [A] -/
#guard_msgs in structure A
/-- info: [Elab.structure.resolutionOrder] computed resolution order: [B, A] -/
#guard_msgs in structure B extends A
/-- info: [Elab.structure.resolutionOrder] computed resolution order: [C, A] -/
#guard_msgs in structure C extends A
/-- info: [Elab.structure.resolutionOrder] computed resolution order: [D, B, C, A] -/
#guard_msgs in structure D extends B, C

def A.x (a : A) : Bool := default
def B.x (b : B) : Nat := default
def A.y (c : A) : Bool := default
def C.y (d : C) : Nat := default

variable (a : A) (b : B) (c : C) (d : D)

/-- info: a.x : Bool -/
#guard_msgs in #check a.x
/-- info: b.x : Nat -/
#guard_msgs in #check b.x
/-- info: c.x : Bool -/
#guard_msgs in #check c.x
/-- info: d.x : Nat -/
#guard_msgs in #check d.x
/-- info: a.y : Bool -/
#guard_msgs in #check a.y
/-- info: b.y : Bool -/
#guard_msgs in #check b.y
/-- info: c.y : Nat -/
#guard_msgs in #check c.y
/-- info: d.toC.y : Nat -/
#guard_msgs in #check d.y


/-!
Example resolution order failure
-/

/--
warning: failed to compute strict resolution order:
- parent 'B' must come after parent 'D'
---
info: [Elab.structure.resolutionOrder] computed resolution order: [D', B, D, C, A]
-/
#guard_msgs in
structure D' extends B, D


/-!
Example from issue 3467.
-/

namespace Issue3467

/-- info: [Elab.structure.resolutionOrder] computed resolution order: [Issue3467.X] -/
#guard_msgs in
structure X where
  base : Nat

/-- info: [Elab.structure.resolutionOrder] computed resolution order: [Issue3467.A, Issue3467.X] -/
#guard_msgs in
structure A extends X where
  countA : Nat

/-- info: [Elab.structure.resolutionOrder] computed resolution order: [Issue3467.B, Issue3467.X] -/
#guard_msgs in
structure B extends X where
  countB : Nat

namespace A

def getTwiceCountA (a : A) := a.countA * 2

end A

namespace B

def getTwiceCountB (b : B) := b.countB * 2

end B

/--
info: [Elab.structure.resolutionOrder] computed resolution order: [Issue3467.C, Issue3467.A, Issue3467.B, Issue3467.X]
-/
#guard_msgs in
structure C extends A, B

def getCounts (c : C) :=
  c.countA + c.countB

def getTwiceCounts (c : C) :=
  c.getTwiceCountA + c.getTwiceCountB
--                     ^^^^ used to fail to resolve

end Issue3467


namespace Issue1881

/-- info: [Elab.structure.resolutionOrder] computed resolution order: [Issue1881.Foo1] -/
#guard_msgs in
structure Foo1 where
  a : Nat
  b : Nat

/-- info: [Elab.structure.resolutionOrder] computed resolution order: [Issue1881.Foo2] -/
#guard_msgs in
structure Foo2 where
  a : Nat
  c : Nat

/--
info: [Elab.structure.resolutionOrder] computed resolution order: [Issue1881.Foo3, Issue1881.Foo1, Issue1881.Foo2]
-/
#guard_msgs in
structure Foo3 extends Foo1, Foo2 where
  d : Nat

def Foo1.bar1 (_ : Foo1) : Nat := 0
def Foo2.bar2 (_ : Foo2) : Nat := 1
example (x : Foo3) := x.bar1 -- works
example (x : Foo3) := x.bar2 -- now works

end Issue1881
