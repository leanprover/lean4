class Approx {α : Type} (a : α) (X : Type) : Type where
  val : X

variable {α β X Y : Type} {f' : α → β} {x' : α} [f : Approx f' (X → Y)] [x : Approx x' X]

-- fails
#check f.val x.val

-- works
#check let f'' := f.val
       let x'' := x.val
       f'' x''
