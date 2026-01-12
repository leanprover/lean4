import «LlvmBitcodeGen»
import Lean
open Lean


def main : IO Unit :=
  IO.println s!"LLVM backend enabled: '{Lean.Internal.hasLLVMBackend ()}'"
