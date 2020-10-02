/-! Parse and reformat file -/
import Lean.PrettyPrinter
new_frontend
open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Format

unsafe def main (args : List String) : IO Unit := do
let (debug, f) : Bool × String := match args with
  | [f, "-d"] => (true, f)
  | [f]       => (false, f)
  | _         => panic! "usage: file [-d]";
let env ← mkEmptyEnvironment;
let stx ← Lean.Parser.parseFile env args.head!;
let (f, _) ← («finally» (PrettyPrinter.ppModule stx) printTraces).toIO { options := Options.empty.setBool `trace.PrettyPrinter.format debug } { env := env };
IO.print f;
let stx' ← Lean.Parser.parseModule env args.head! (toString f);
pure ()
when (stx' != stx) $
  let stx := stx.getArg 1;
  let stx' := stx'.getArg 1;
  stx.getArgs.size.forM fun i =>
    when (stx.getArg i != stx'.getArg i) $
      throw $ IO.userError $ "reparsing failed:\n" ++ toString (stx.getArg i) ++ "\n" ++ toString (stx'.getArg i)

#eval main ["../../../src/Init/Core.lean"]
