class Approx {α : Type} (a : α) (X : Type) : Type where
  val : X

variable {α β X Y : Type} {f' : α → β} {x' : α} [f : Approx f' (X → Y)] [x : Approx x' X]

-- fails
/-- info: Approx.val f' (Approx.val x') : Y -/
#guard_msgs in
#check f.val x.val

-- works
/--
info: let f'' := Approx.val f';
let x'' := Approx.val x';
f'' x'' : Y
-/
#guard_msgs in
#check let f'' := f.val
       let x'' := x.val
       f'' x''
