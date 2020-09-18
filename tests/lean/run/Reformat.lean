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
env ← mkEmptyEnvironment;
stx ← Lean.Parser.parseFile env args.head!;
(f, _) ← (finally (PrettyPrinter.ppModule stx) printTraces).toIO { options := Options.empty.setBool `trace.PrettyPrinter.parenthesize debug } { env := env };
IO.print f;
--stx' ← Lean.Parser.parseModule env args.head! (toString f);
pure ()
-- TODO: this doesn't quite work yet because the parenthesizer adds unnecessary parentheses in one case
/-
when (stx' != stx) $
  stx.getArgs.size.forM fun i =>
    when (stx.getArg i != stx'.getArg i) $
      throw $ IO.userError $ "reparsing failed:\n" ++ toString (stx.getArg i) ++ "\n" ++ toString (stx'.getArg i)
      -/

#eval main ["../../../src/Init/Core.lean"]
