Set pp::colors false
Show fun x : Bool, (fun x : Bool, x).
Show let x := true,
         y := true
     in (let z := x /\ y,
             f := (fun x y : Bool, x /\ y <=>
                                   y /\ x <=>
                                   x \/ y \/ y)
         in (f x y) \/ z)
