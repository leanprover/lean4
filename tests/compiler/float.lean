def tst1 : IO Unit := do
IO.println (1 : Float);
IO.println ((1 : Float) + 2);
IO.println ((2 : Float) - 3);
IO.println ((3 : Float) * 2);
IO.println ((3 : Float) / 2);
IO.println (decide ((3 : Float) < 2));
IO.println (decide ((3 : Float) < 4));
IO.println (decide ((3 : Float) = 2));
IO.println (decide ((2 : Float) = 2));
IO.println (decide ((3 : Float) ≤ 2));
IO.println (decide ((3 : Float) ≤ 3));
IO.println (decide ((3 : Float) ≤ 4));
pure ()

structure Foo :=
(x : Nat)
(w : UInt64)
(y : Float)
(z : Float)

@[noinline] def mkFoo (x : Nat) : Foo :=
{ x := x, w := x.toUInt64, y := x.toFloat / 3, z := x.toFloat / 2 }

def tst2 (x : Nat) : IO Unit := do
let foo := mkFoo x;
IO.println foo.y;
IO.println foo.z

def main : IO Unit := do
tst1;
IO.println "-----";
tst2 7;
pure ()
