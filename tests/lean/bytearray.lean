
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

#eval [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88].toByteArray.toUInt64LE! == 0x1122334455667788
#eval [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88].toByteArray.toUInt64BE! == 0x8877665544332211
