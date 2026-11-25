/-!
`warn.repeatedInstanceRejections`: at the end of a declaration, Lean warns about each assignment to
an instance metavariable that `isDefEq` rejected at least that many times. Here `?d : @Dep Nat instB1`
meets `instD2 : @Dep Nat instB2`. The two `B Nat` instances differ, so the instance-type check
rejects `?d := instD2`. The layers `L (k+1) := L k + L k` make `isDefEq` retry the same failing
comparison, and with it the same rejected assignment, many times.
-/

set_option warn.classDefReducibility false

class B (α : Type) where n : Nat
class Dep (α : Type) [B α] where dval : Nat

def instB1 : B Nat := ⟨1⟩
def instB2 : B Nat := ⟨2⟩
def instD2 : @Dep Nat instB2 := @Dep.mk Nat instB2 2

def L0 (α : Type) [B α] (d : Dep α) : Nat := d.dval + B.n α
def L1 (α : Type) [B α] (d : Dep α) : Nat := L0 α d + L0 α d
def L2 (α : Type) [B α] (d : Dep α) : Nat := L1 α d + L1 α d
def L3 (α : Type) [B α] (d : Dep α) : Nat := L2 α d + L2 α d

def P (n : Nat) : Prop := n = n

/--
error: Type mismatch
  h
has type
  P (L3 Nat instD2)
but is expected to have type
  P (L3 Nat ?m.3)
---
warning: `isDefEq` rejected the same instance assignment many times: the type of the value does not agree with the type of the instance metavariable at `.instances` transparency, and no synthesized instance of that type is defeq to the value:

10236 times: the assignment of
  { dval := 2 }
of type
  @Dep Nat instB2
to an instance metavariable of type
  @Dep Nat instB1

5628 times: the assignment of
  instD2
of type
  @Dep Nat instB2
to an instance metavariable of type
  @Dep Nat instB1

Note: Repeated failing comparisons can make elaboration slow or exhaust the heartbeats. Disable this warning with `set_option warn.repeatedInstanceRejections 0`.
-/
#guard_msgs in
set_option warn.repeatedInstanceRejections 16 in
example (h : P (@L3 Nat instB2 instD2)) : True := by
  have := (h : P (@L3 Nat instB1 _))
  trivial

/-! Below the threshold, and with the warning switched off, there is no warning. -/

/--
error: Type mismatch
  h
has type
  P (L3 Nat instD2)
but is expected to have type
  P (L3 Nat ?m.3)
-/
#guard_msgs in
set_option warn.repeatedInstanceRejections 0 in
example (h : P (@L3 Nat instB2 instD2)) : True := by
  have := (h : P (@L3 Nat instB1 _))
  trivial
