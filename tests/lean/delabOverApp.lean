def add (f g : Nat → Nat) : Nat → Nat := fun x => f x + g x

@[app_unexpander add]
def unexpandAdd : Lean.PrettyPrinter.Unexpander
  | `($_ $f $g) => `($f + $g)
  | _ => throw ()

variable (f g : Nat → Nat)
#check add f g
#check add f g 1
