import Lake
import Lean
open Lean
open Lake DSL

package «llvm-bitcode-gen» where
  -- add package configuration options here
  backend := .llvm

lean_lib «LlvmBitcodeGen» where
  -- add library configuration options here

@[default_target]
lean_exe «llvm-bitcode-gen» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

script hasLLVMBackend do
  IO.println s!"Lake Lean.Internal.hasLLVMBackend: {Lean.Internal.hasLLVMBackend ()}"
  return 0

