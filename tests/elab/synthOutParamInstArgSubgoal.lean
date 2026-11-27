/-!
Instance search defers the unification of an instance argument in an output position of a
subgoal until the subgoal has an answer. Here the subgoal `@C (StateT Nat Id) ?P (B.toA ?l)` of
the `T` instance is solved as `@C (StateT Nat Id) ?P ?o`, and `B.toA ?l` is unified with the
answer's order once `?P` is known.
-/

class A (α : Type) where a : Nat
class B (α : Type) extends A α
instance : A Prop := ⟨0⟩
instance : B Prop := {}
instance [A α] : A (Nat → α) := ⟨A.a α⟩
instance [B α] : B (Nat → α) := {}

class C (m : Type → Type) (P : outParam Type) [A P] : Prop
instance : C Id Prop := ⟨⟩
instance [A P] [C m P] : C (StateT Nat m) (Nat → P) := ⟨⟩

def T (m : Type → Type) := m
instance [B P] [C m P] : C (T m) P := ⟨⟩

example : @C (T Id) Prop _ := inferInstance
example : @C (T (StateT Nat Id)) (Nat → Prop) _ := inferInstance
example : @C (T (StateT Nat (StateT Nat Id))) (Nat → Nat → Prop) _ := inferInstance

/-- info: inferInstance : C (T (StateT Nat Id)) (Nat → Prop) -/
#guard_msgs in
#check (inferInstance : @C (T (StateT Nat Id)) _ _)
