print (fun x : Bool, (fun y : Bool, x /\ y))
print let x := true,
         y := true
     in (let z := x /\ y,
             f := (fun arg1 arg2 : Bool, arg1 /\ arg2 =
                                         arg2 /\ arg1 =
                                         arg1 \/ arg2 \/ arg2)
         in (f x y) \/ z)
eval let x := true,
         y := true,
         z := x /\ y,
         f := (fun arg1 arg2 : Bool, arg1 /\ arg2 =
                                     arg2 /\ arg1 =
                                     arg1 \/ arg2 \/ arg2)
     in (f x y) \/ z
