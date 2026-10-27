

def tst : IO Unit :=
do
let bs := [(1 : Float), 2, 3].toFloatArray;
IO.println bs;
let bs := bs.push (4 : Float);
let bs := bs.set! 1 (20 / 3);
IO.println bs;
let bs₁ := bs.set! 2 30;
IO.println bs₁;
IO.println bs;
IO.println bs.size;
pure ()

/--
info: [1.0, 2.0, 3.0]
[1.0, 6.666666666666667, 3.0, 4.0]
[1.0, 6.666666666666667, 30.0, 4.0]
[1.0, 6.666666666666667, 3.0, 4.0]
4
-/
#guard_msgs in
#eval tst
