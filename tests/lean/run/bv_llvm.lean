import Std.Tactic.BVDecide
import Init.System.IO
open BitVec
-- (x % -y + y).getLsbD i

def testabc : IO Unit :=
  have w := 4
  for xx in [0 : 2^w] do
    for yy in [0 : 2^w] do


      IO.println ""
    IO.println ""

#eval testabc
