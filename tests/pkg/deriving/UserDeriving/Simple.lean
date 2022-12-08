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

def mkMyInhabitedHandler (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let cmd ← `(def $(mkIdent (declName ++ `test)) := 0)
    elabCommand cmd
  return false -- `false` instructs Lean to run the next handler

initialize
  registerDerivingHandler ``Simple mkSimpleHandler
  registerDerivingHandler ``Inhabited mkMyInhabitedHandler