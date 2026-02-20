def Construction : List Unit → Type
| []     => Unit
| _ :: _ => Unit → Unit

@[inline]
def List.asConstruction : (l : List Unit) → Construction l
| []      => ()
| _ :: _ => λ _ => ()

def f1 : List Unit := List.replicate 1 ()
def value : Unit := f1.asConstruction ()

/-- info: () -/
#guard_msgs in
#eval IO.println value
