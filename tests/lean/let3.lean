import Int.

variable magic : Pi (H : Bool), H

set::option pp::notation false
set::option pp::coercion true
print let a : Int   := 1,
         H : a > 0 := magic (a > 0)
     in H