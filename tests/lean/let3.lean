import Int.

variable magic : forall (H : Bool), H

set_option pp::notation false
set_option pp::coercion true
print let a : Int   := 1,
         H : a > 0 := magic (a > 0)
     in H