--  RUN: ./validate-lean.sh %s
--  run: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET

--- CHECK-INTERPRET: 1
--- CHECK-INTERPRET: 0
--- CHECK-INTERPRET: 1
--- CHECK-INTERPRET: 0

-- run: lean %s 2>&1 | hask-opt   --lean-lower  --ptr-lower | mlir-translate --mlir-to-llvmir |  opt -O3 -S | FileCheck %s --check-prefix=CHECK-LLVM

-- | todo: make this a better regex based match.
-- CHECK-LLVM: define i8* @l_even(i8* %0) local_unnamed_addr !dbg !3 {
-- CHECK-LLVM: tailrecurse
-- CHECK-LLVM: l_odd.exit
-- CHECK-LLVM: }


-- TODO: why is a join point created?
-- func @l_even(%arg0: !lz.value) -> !lz.value {
--   %0 = call @l_odd(%arg0) : (!lz.value) -> !lz.value
--   lz.return %0 : !lz.value
-- }
-- func @l_odd(%arg0: !lz.value) -> !lz.value {
--   %0 = call @l_even(%arg0) : (!lz.value) -> !lz.value
--   lz.return %0 : !lz.value
-- }

set_option trace.compiler.ir.init true

mutual 
  partial def even (a : Nat) : Nat := if a == 0 then 1 else odd (a - 1)
  partial def odd (a : Nat) : Nat := if a == 0 then 0 else even (a - 1)
end

-- | This example is not so interesting because dead code elimination gets rid of the work.
def main (xs: List String) : IO Unit := do
   IO.println (even 0)
   IO.println (even 1)
   IO.println (even 2)
   IO.println (even 3)


