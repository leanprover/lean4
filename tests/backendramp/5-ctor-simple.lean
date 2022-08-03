--  RUN: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET
--  RUN: ./validate-lean.sh %s 
-- CHECK-INTERPRET: ctor

-- set_option trace.compiler.ir.init true
inductive Ctor
| mk
deriving Inhabited

def Ctor.toString: Ctor -> String
| .mk => "ctor"

def main (xs: List String) : IO Unit := 
  IO.println (Ctor.mk.toString)
