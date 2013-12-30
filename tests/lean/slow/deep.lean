Import int.
Definition f1 (f : Int -> Int) (x : Int) : Int := f (f (f (f x)))
Definition f2 (f : Int -> Int) (x : Int) : Int := f1 (f1 (f1 (f1 f))) x
Definition f3 (f : Int -> Int) (x : Int) : Int := f1 (f2 (f2 f)) x
Variable f : Int -> Int.
SetOption pp::width 80.
SetOption lean::pp::max_depth 2000.
Eval f3 f 0.