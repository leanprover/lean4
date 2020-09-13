new_frontend
def tst : IO Unit :=
do
let bs := [1, 2, 3].toByteArray;
IO.println bs;
let bs := bs.push 4;
let bs := bs.set! 1 20;
IO.println bs;
let bs₁ := bs.set! 2 30;
IO.println bs₁;
IO.println bs;
IO.println bs.size;
IO.println (bs ++ bs);
IO.println (bs.extract 1 3);
pure ()

#eval tst
