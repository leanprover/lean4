--  RUN: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET
--  RUN: ./validate-lean.sh %s 


-- 4 + 3 + 2 + 1 = 10
-- CHECK-INTERPRET: 10

set_option trace.compiler.ir.init true

def mkRandomArray : Nat -> Array Nat -> Array Nat
| 0,   as => as
| i+1, as => mkRandomArray i (as.push (i+1))

-- | sumAux <length> arr[0..length-1]
def sumAux : Nat -> Array Nat -> Nat
| 0, arr => 0
| ix+1, arr => arr[ix] + sumAux ix arr


def main (xs: List String) : IO Unit := 
  let len := 4; let tot := sumAux len (mkRandomArray len Array.empty); IO.println (toString tot)

