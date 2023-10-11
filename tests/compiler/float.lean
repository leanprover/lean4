
def tst1 : IO Unit := do
  IO.println (1 : Float)
  IO.println ((1 : Float) + 2)
  IO.println ((2 : Float) - 3)
  IO.println ((3 : Float) * 2)
  IO.println ((3 : Float) / 2)
  IO.println (decide ((3 : Float) < 2))
  IO.println (decide ((3 : Float) < 4))
  IO.println ((3 : Float) == 2)
  IO.println ((2 : Float) == 2)
  IO.println (decide ((3 : Float) ≤ 2))
  IO.println (decide ((3 : Float) ≤ 3))
  IO.println (decide ((3 : Float) ≤ 4))
  IO.println (Float.ofInt 0)
  IO.println (Float.ofInt 42)
  IO.println (Float.ofInt (-42))
  IO.println (0 / 0 : Float).toUInt8
  IO.println (0 / 0 : Float).toUInt16
  IO.println (0 / 0 : Float).toUInt32
  IO.println (0 / 0 : Float).toUInt64
  IO.println (-1 : Float).toUInt8
  IO.println (256 : Float).toUInt8
  IO.println (1 / 0 : Float).toUInt8
  IO.println (-1 : Float).toUInt64
  IO.println (2^64 : Float).toUInt64
  IO.println (1 / 0 : Float).toUInt64
  IO.println (let x : Float := 1.4; (x, x.isNaN, x.isInf, x.isFinite, x.frExp))
  IO.println (let x : Float := 0 / 0; (x, x.isNaN, x.isInf, x.isFinite, x.frExp))
  IO.println (let x : Float := -0 / 0; (x, x.isNaN, x.isInf, x.isFinite, x.frExp))
  IO.println (let x : Float := 1 / 0; (x, x.isNaN, x.isInf, x.isFinite, x.frExp))
  IO.println (let x : Float := -1 / 0; (x, x.isNaN, x.isInf, x.isFinite, x.frExp))
  -- Pow instance defaults to exponent being a Float:
  IO.println (2^(-1) : Float)
  IO.println (2.2^2.2 : Float)

structure Foo where
  x : Nat
  w : UInt64
  y : Float
  z : Float

@[noinline] def mkFoo (x : Nat) : Foo :=
  { x := x, w := x.toUInt64, y := x.toFloat / 3, z := x.toFloat / 2 }

def tst2 (x : Nat) : IO Unit := do
  let foo := mkFoo x
  IO.println foo.y
  IO.println foo.z

@[noinline] def fMap (f : Float → Float) (xs : List Float) :=
  xs.map f

def tst3 (xs : List Float) (y : Float) : IO Unit :=
  IO.println (fMap (fun x => x / y) xs)

def tst4 (xs : List Float) : IO Unit :=
  IO.println (fMap (fun x => x.abs) xs)

def main : IO Unit := do
  tst1
  IO.println "-----"
  tst2 7
  tst3 [3, 4, 7, 8, 9, 11] 2
  tst4 [3, -3, 0, -0, -1 / 0, -0 / 0]
