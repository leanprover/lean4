import Int.

variable magic : Pi (H : Bool), H

setoption pp::notation false
setoption pp::coercion true
print let a : Int   := 1,
         H : a > 0 := magic (a > 0)
     in H