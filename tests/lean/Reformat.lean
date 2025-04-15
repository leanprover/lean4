import Lean.PrettyPrinter
/-! Parse and reformat file -/

open Lean
open Lean.Elab
open Lean.Elab.Term
open Std.Format open Std

unsafe def main (args : List String) : IO Unit := do
let (debug, f) : Bool × String := match args with
  | [f, "-d"] => (true, f)
  | [f]       => (false, f)
  | _         => panic! "usage: file [-d]"
let env ← mkEmptyEnvironment
let stx ← Lean.Parser.testParseFile env args.head!
let (f, _) ← (tryFinally (PrettyPrinter.ppModule stx) printTraces).toIO { options := Options.empty.setBool `trace.PrettyPrinter.format debug, fileName := "", fileMap := default } { env := env }
IO.print f
let stx' ← Lean.Parser.testParseModule env args.head! (toString f)
if stx' != stx then
  let stx := stx.raw.getArg 1
  let stx' := stx'.raw.getArg 1
  stx.getArgs.size.forM fun i _ => do
    if stx.getArg i != stx'.getArg i then
      throw $ IO.userError s!"reparsing failed:\n{stx.getArg i}\n{stx'.getArg i}"

-- abbreviated Prelude.lean, which can be parsed without elaboration
#eval main ["Reformat/Input.lean"]
