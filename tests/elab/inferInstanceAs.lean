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
info: @[implicit_reducible] private def instCD2._aux_1 : C D2 :=
instCI2
-/
#guard_msgs in
#print instCD2._aux_1
