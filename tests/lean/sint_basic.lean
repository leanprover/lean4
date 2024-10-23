#check Int8
#eval Int8.ofInt 20
#eval Int8.ofInt (-20)
#eval Int8.ofInt (-20)  = -20
#eval Int8.ofInt (-130) = 126
#eval (10 : Int8) ≠ (11 : Int8)
#eval (-10 : Int8) ≠ (10 : Int8)
#eval Int8.ofNat 10 = 10
#eval Int8.ofNat 130 = 130
#eval Int8.ofNat 120 = 120
#eval Int8.ofInt (-20) = -20
#eval (Int8.ofInt (-2)).toInt = -2
#eval (Int8.ofInt (-2)).toNat = 0
#eval (Int8.ofInt (10)).toNat = 10
#eval (Int8.ofInt (10)).toInt = 10
#eval Int8.ofNat (2^64) == 0
#eval Int8.ofInt (-2^64) == 0
#eval Int8.neg 10 = -10
#eval (20 : Int8) + 20 = 40
#eval (127 : Int8) + 1 = -128
#eval (-10 : Int8) + 10 = 0
#eval (1 : Int8) - 2 = -1
#eval (-128 : Int8) - 1 = 127
#eval (1 : Int8) * 120 = 120
#eval (2 : Int8) * 10 = 20
#eval (2 : Int8) * 128 = 0
#eval (-1 : Int8) * (-1) = 1
#eval (1 : Int8) * (-1) = -1
#eval (2 : Int8) * (-10) = -20
#eval (-5 : Int8) * (-5) = 25
#eval (10 : Int8) / 2 = 5
#eval (-10 : Int8) / 2 = -5
#eval (-10 : Int8) / -2 = 5
#eval (10 : Int8) / -2 = -5
#eval (10 : Int8) / 0 = 0
#eval (10 : Int8) % 1 = 0
#eval (10 : Int8) % 0 = 0
#eval (10 : Int8) % 3 = 1
#eval (-10 : Int8) % 3 = -1
#eval (-10 : Int8) % -3 = -1
#eval (10 : Int8) % -3 = 1
#eval (10 : Int8) &&& 10 = 10
#eval (-1 : Int8) &&& 1 = 1
#eval (-1 : Int8) ^^^ 123 = ~~~123
#eval (10 : Int8) ||| 10 = 10
#eval (10 : Int8) ||| 0 = 10
#eval (10 : Int8) ||| -1 = -1
#eval (16 : Int8) >>> 1 = 8
#eval (16 : Int8) >>> 16 = 16
#eval (16 : Int8) >>> 9 = 8
#eval (-16 : Int8) >>> 1 = -8
#eval (16 : Int8) <<< 1 = 32
#eval (16 : Int8) <<< 9 = 32
#eval (-16 : Int8) <<< 1 = -32
#eval (-16 : Int8) <<< 9 = -32
#eval (-16 : Int8) >>> 1 <<< 1 = -16
#eval (0 : Int8) < 1
#eval (0 : Int8) < 120
#eval (120 : Int8) > 0
#eval -1 < (0 : Int8)
#eval -120 < (0 : Int8)
#eval ¬((0 : Int8) < (0 : Int8))
#eval (0 : Int8) ≤ 1
#eval (0 : Int8) ≤ 120
#eval -1 ≤ (0 : Int8)
#eval -120 ≤ (0 : Int8)
#eval (0 : Int8) ≤ (0 : Int8)
#eval (-10 : Int8) ≥ (-10 : Int8)
#eval max (10 : Int8) 20 = 20
#eval max (10 : Int8) (-1) = 10
#eval min (10 : Int8) 20 = 10
#eval min (10 : Int8) (-1) = -1

def test : Option Int := Id.run do
  let doTest (base : Int) (i : Int) : Bool :=
    let t := base + i
    let a := ⟨⟨BitVec.ofInt 8 t⟩⟩
    let b := Int8.ofInt t
    a == b

  let range := 2^9
  
  for i in [0:2*range] do
    let i := Int.ofNat i - range
    if !(doTest (2^256) i) then
      return i
    if !(doTest (-2^256) i) then
      return i
  return none

#eval test.isNone

-- runtime representation
set_option trace.compiler.ir.result true in
def myId (x : Int8) : Int8 := x
