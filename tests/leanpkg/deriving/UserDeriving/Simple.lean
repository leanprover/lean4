import Lean

class Simple (α : Type u) where
  val : α

open Lean
open Lean.Elab
open Lean.Elab.Command
def mkSimpleHandler (declNames : Array Name) : CommandElabM Bool := do
  dbg_trace ">> mkSimpleHandler {declNames}"
  -- TODO: see examples at src/Lean/Elab/Deriving
  return true

initialize
  registerBuiltinDerivingHandler ``Simple mkSimpleHandler
