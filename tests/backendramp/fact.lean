--  RUN: ./validate-lean.sh %s
--  run: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET


partial def fact : Nat -> Nat ->  Nat
 | 0, k => k 
 | a, k => fact (a - 1) (a*k)

unsafe def main : List String → IO Unit
| [s] => do
  let n := s.toNat!;
  IO.println (fact n 1)
| _ => return ()


