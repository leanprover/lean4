Import Int.

Variable magic : Pi (H : Bool), H

SetOption pp::notation false
SetOption pp::coercion true
Show let a : Int   := 1,
         H : a > 0 := magic (a > 0)
     in H