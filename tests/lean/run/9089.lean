example : ((let f := @Bool.rec (fun _ => Bool × Unit) (false, ()) (true, ()); f) true).1 = true := rfl
