

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
info: [1.000000, 2.000000, 3.000000]
[1.000000, 6.666667, 3.000000, 4.000000]
[1.000000, 6.666667, 30.000000, 4.000000]
[1.000000, 6.666667, 3.000000, 4.000000]
4
-/
#guard_msgs in
#eval tst
