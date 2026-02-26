import Lean.PrettyPrinter
/-! Parse and reformat file -/

open Lean
open Lean.Elab
open Lean.Elab.Term
open Std.Format open Std

unsafe def main (args : List String) : IO Unit := do
  let (debug, fn) : Bool × String := match args with
    | [f, "-d"] => (true, f)
    | [f]       => (false, f)
    | _         => panic! "usage: file [-d]"
  let env ← mkEmptyEnvironment
  let stx ← Lean.Parser.testParseFile env fn
  let act : CoreM Format := do
    withOptions (fun opts =>
        opts
          -- Name sanitization clears inline comments attached to identifiers.
          |>.set `pp.sanitizeNames false
          |>.set `trace.PrettyPrinter.format debug) do
      tryFinally (PrettyPrinter.ppModule stx) printTraces
  let (f, _) ← act.toIO { fileName := "", fileMap := default } { env := env }
  IO.print f
  let stx' ← Lean.Parser.testParseModule env fn (toString f)
  if stx' != stx then
    let stx := stx.raw.getArg 1
    let stx' := stx'.raw.getArg 1
    stx.getArgs.size.forM fun i _ => do
      if stx.getArg i != stx'.getArg i then
        throw $ IO.userError s!"reparsing failed:\n{stx.getArg i}\n{stx'.getArg i}"

-- abbreviated Prelude.lean, which can be parsed without elaboration
#eval main ["Reformat.lean.input"]
