--  RUN: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET
--  RUN: ./validate-lean.sh %s 

--  run: lean %s 2>&1 1>/dev/null | hask-opt  --lz-canonicalize --lz-interpret=mode=lambdapure | FileCheck %s --check-prefix=CHECK-INTERPRET

-- CHECK-INTERPRET: 10
-- CHECK-INTERPRET: 20
-- CHECK-INTERPRET: 3
-- CHECK-INTERPRET: 4

set_option trace.compiler.ir.init true
def casef : Nat -> Nat
| 0 => 10
| 1 => 20
| x => x + 1

-- | This example is not so interesting because dead code elimination gets rid of the work.
def main (xs: List String) : IO Unit := do
   IO.println (casef 0)
   IO.println (casef 1)
   IO.println (casef 2)
   IO.println (casef 3)


