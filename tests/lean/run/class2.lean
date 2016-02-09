import logic data.prod data.num
open prod nonempty inhabited

theorem H {A B : Type} (H1 : inhabited A) : inhabited (Prop × A × (B → num))
:= _
reveal H
print H
