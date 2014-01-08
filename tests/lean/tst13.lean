print fun x : Bool, (fun x : Bool, x).
print let x := true,
         y := true
     in (let z := x /\ y,
             f := (fun x y : Bool, x /\ y =
                                   y /\ x =
                                   x \/ y \/ y)
         in (f x y) \/ z)
