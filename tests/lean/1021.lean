import Lean
open Lean Meta
#eval show MetaM _ from do
  findDeclarationRanges? `Lean.Elab.Term.expandAssert
set_option trace.Meta.synthInstance true
#synth MonadError MetaM
