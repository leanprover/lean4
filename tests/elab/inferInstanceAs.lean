module

class C (α : Type) where
  c : α → α

/-! Trivial data wrapper -/

axiom I : Type
instance : C I where
  c x := x

def D := I

instance : C D := inferInstanceAs (C I)

-- We can still use it as an `inferInstance` synonym in the old mode
set_option backward.inferInstanceAs.wrap false in
/-- info: «inferInstanceAs» (C D) : C D -/
#guard_msgs in
#check inferInstanceAs (C D)

/--
info: @[implicit_reducible] private def instCD : C D :=
{ c := instCD._aux_1 }
-/
#guard_msgs in
#print instCD
/--
info: private def instCD._aux_1 : D → D :=
fun x => x
-/
#guard_msgs in
#print instCD._aux_1

/-! Irreducible instances are wrapped as is. -/

axiom I2 : Type
@[instance] opaque instCI2 : C I2 := { c := fun x => x }
def D2 := I2

instance : C D2 := inferInstanceAs (C I2)
/--
info: @[implicit_reducible] private def instCD2 : C D2 :=
instCD2._aux_1
-/
#guard_msgs in
#print instCD2
/--
info: private def instCD2._aux_1 : C D2 :=
instCI2
-/
#guard_msgs in
#print instCD2._aux_1

/-! Flattened inheritance test. -/

class Base (α : Type) where
  b : α

class Foo (α : Type) extends Base α where
  a : α

class Bar (α : Type) extends Base α where
  c : α

class FooBar (α : Type) extends Foo α, Bar α

instance : FooBar Nat where
  a := 0
  b := 1
  c := 2

def MyNat := Nat
deriving Foo, Bar, FooBar

theorem zou : instFooBarMyNat.toBar = instBarMyNat := by
  with_reducible_and_instances rfl

/-! Non-constructor instances should be used as is. -/

@[macro_inline, implicit_reducible]
def dite' {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  h.casesOn e t

instance Nat.decLe' (n m : @& Nat) : Decidable (LE.le n m) :=
  dite' (Eq (Nat.ble n m) true) (fun h => isTrue (Nat.le_of_ble_eq_true h)) (fun h => isFalse (Nat.not_le_of_not_ble_eq_true h))

#guard_msgs in
instance (x y : BitVec w) : Decidable (LE.le x y) :=
  (inferInstance : Decidable (LE.le x.toNat y.toNat))

instance (x y : BitVec w) : Decidable (LE.le x y) :=
  inferInstanceAs (Decidable (LE.le x.toNat y.toNat))

/-! Universes can be introduced by synth and need to be unified with the expected type properly. -/

structure MyStruct where
  x : PUnit.{u + 1} := ⟨⟩
  y : PUnit.{v + 1} := ⟨⟩

instance : Zero MyStruct.{u, max u v} := ⟨{}⟩

instance : Zero MyStruct.{u, max u v} := inferInstanceAs <| Zero MyStruct.{u, max u v}

/-! Test reusing subinstances not encountered directly. -/

class Base2 (α : Type) where
  a : α

class Main0 (α : Type) extends Base2 α where
  b : α

class Main1 (α : Type) extends Base2 α where
  c : α

class Super (α : Type) extends Main0 α, Main1 α where

def MyCopy (α : Type) : Type := α

instance iBase2 (α : Type) [Base2 α] : Base2 (MyCopy α) :=
  inferInstanceAs <| Base2 α

instance iMain0 (α : Type) [Main0 α] : Main0 (MyCopy α) :=
  inferInstanceAs <| Main0 α

instance iMain1 (α : Type) [Main1 α] : Main1 (MyCopy α) :=
  inferInstanceAs <| Main1 α

instance iSuper (α : Type) [Super α] : Super (MyCopy α) :=
  inferInstanceAs <| Super α

example (α : Type) [Super α] :
    (iSuper α).toMain1 = iMain1 α := by
  with_reducible_and_instances rfl

/--
info: @[implicit_reducible] private def iSuper : (α : Type) → [Super α] → Super (MyCopy α) :=
fun α [Super α] => { toMain0 := iMain0 α, c := Main1.c }
-/
#guard_msgs in
#print iSuper
