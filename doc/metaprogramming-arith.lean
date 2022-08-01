inductive Arith : Type
  | add : Arith → Arith → Arith  -- e + f
  | mul : Arith → Arith → Arith  -- e * f
  | int : Int → Arith  -- constant
  | symbol : String → Arith  -- variable

declare_syntax_cat arith

syntax num : arith  -- int for Arith.int
syntax str : arith  -- strings for Arith.symbol
syntax:60 arith:60 "+" arith:61 : arith  -- Arith.add
syntax:70 arith:70 "*" arith:71 : arith  -- Arith.mul
syntax "(" arith ")" : arith  -- parenthesized expressions

-- auxiliary notation for translating `arith` into `term`
syntax "`[Arith| " arith "]" : term

macro_rules
  | `(`[Arith| $s:str]) => `(Arith.symbol $s)
  | `(`[Arith| $num:num]) => `(Arith.int $num)
  | `(`[Arith| $x + $y]) => `(Arith.add `[Arith| $x] `[Arith| $y])
  | `(`[Arith| $x * $y]) => `(Arith.mul `[Arith| $x] `[Arith| $y])
  | `(`[Arith| ($x)]) => `(`[Arith| $x])

#check `[Arith| "x" * "y"]  -- mul
-- Arith.mul (Arith.symbol "x") (Arith.symbol "y")

#check `[Arith| "x" + "y"]  -- add
-- Arith.add (Arith.symbol "x") (Arith.symbol "y")

#check `[Arith| "x" + 20]  -- symbol + int
-- Arith.add (Arith.symbol "x") (Arith.int 20)

#check `[Arith| "x" + "y" * "z"]  -- precedence
-- Arith.add (Arith.symbol "x") (Arith.mul (Arith.symbol "y") (Arith.symbol "z"))

#check `[Arith| "x" * "y" + "z"]  -- precedence
-- Arith.add (Arith.mul (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")

#check `[Arith| ("x" + "y") * "z"]  -- parentheses
-- Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")

syntax ident : arith

macro_rules
  | `(`[Arith| $x:ident]) => `(Arith.symbol $(Lean.quote (toString x.getId)))

#check `[Arith| x]  -- Arith.symbol "x"

def xPlusY := `[Arith| x + y]
#print xPlusY  -- def xPlusY : Arith := Arith.add (Arith.symbol "x") (Arith.symbol "y")

syntax "<[" term "]>" : arith  -- escape for embedding terms into `Arith`

macro_rules
  | `(`[Arith| <[ $e:term ]>]) => pure e

#check `[Arith| <[ xPlusY ]> + z]  -- Arith.add xPlusY (Arith.symbol "z")
