--  RUN: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET
--  RUN: ./validate-lean.sh %s 
-- CHECK-INTERPRET: ctor

set_option trace.compiler.ir.init true
inductive Ctor
| MkCtor
open Ctor

instance : Inhabited Ctor := ⟨MkCtor⟩

def ctorToStr: Ctor -> String
| MkCtor => "ctor"


def main (xs: List String) : IO Unit := 
  IO.println (ctorToStr (MkCtor))
