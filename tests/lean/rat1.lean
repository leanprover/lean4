import Lean.Data.Rat
open Lean

#eval (15 : Rat) / 10
#eval (15 : Rat) / 10 + 2
#eval (15 : Rat) / 10 - 2
#eval (-2 : Rat).inv
#eval (2 :  Rat).inv == (1 : Rat) / 2
#eval (-2 :  Rat).inv == (-1 : Rat) / 2
#eval (4 : Rat)/9 * (3 : Rat)/10
#eval (4 : Rat)/9 * (-3 : Rat)/10
#eval (1 : Rat) < (-1 : Rat)
#eval (-1 : Rat) < (1 : Rat)
#eval (-1 : Rat)/2 < (1 : Rat)
#eval (-1 : Rat) < 0
#eval (-1 : Rat)/2 < 0
#eval 0 < (-1 : Rat)/2
#eval (1 : Rat)/3 < (1 : Rat)/2
#eval (1 : Rat)/2 < (1 : Rat)/3
-- TODO: add more tests
