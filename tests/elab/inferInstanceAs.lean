module

class C (α : Type) where
  c : α → α

axiom I : Type
instance : C I where
  c x := x

def D := I

instance : C D := inferInstanceAs (C I)

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
