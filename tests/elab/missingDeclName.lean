def foo {α β : Type} (xs : Array (α × β)) (H : true = xs.all fun (x, y) => true) : Unit := ()
