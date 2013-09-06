
Variable magic : Pi (H : Bool), H

Set pp::notation false
Set pp::coercion true
Show let a : Int   := 1,
         H : a > 0 := magic (a > 0)
     in H