

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

#eval tst
