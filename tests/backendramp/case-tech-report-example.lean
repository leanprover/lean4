-- RUN: ./validate-lean.sh %s
--  run: lean %s 2>&1 1>/dev/null | hask-opt --lz-canonicalize  | FileCheck %s
--  run: lean %s 2>&1 1>/dev/null | hask-opt --lz-canonicalize --lz-lambdapure-destructive-updates | FileCheck %s
--  run: lean %s 2>&1 1>/dev/null | hask-opt --lz-canonicalize --lz-lambdapure-destructive-updates --lz-lambdapure-reference-rewriter | FileCheck %s
--  run: lean %s 2>&1 1>/dev/null | hask-opt --lz-canonicalize --lz-interpret=mode=lambdapure | FileCheck %s --check-prefix=CHECK-INTERPRET
--  run: lean %s 2>&1 1>/dev/null | hask-opt --lz-canonicalize  --lz-lower

-- CHECK: func @filter
-- we only keep elements that are not greater than 5, starting from 0.
-- So that gives us  0 <= x <= 5, which is 6 elements.
-- CHECK-INTERPRET: 6
-- CHECK-INTERPRET: constructor(0 1 420)

set_option trace.compiler.ir.init true
set_option compiler.extract_closed false
inductive L
| Nil
| Cons : Nat -> L -> L

open L
instance : Inhabited L := ⟨Nil⟩

def length : L -> Nat
| Nil => 0
| Cons n l => 1 + length l


partial def make' : Nat -> Nat -> L
| n,d =>
  if d = 0 then Cons n Nil
  else Cons (n-d) (make' n (d -1))

def make (n : Nat) : L := make' n n

def main : IO Unit := let l := length (make 50000); IO.println (toString l)
