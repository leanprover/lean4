--
open Lean
def check (b : Bool) : IO Unit :=
unless b do throw $ IO.userError "check failed"

def test1 : IO Unit := do
let x := `x;
let x := addMacroScope `main x 1;
IO.println $ x;
let v := extractMacroScopes x;
let x := { v with name := `y }.review;
IO.println $ x;
let v := extractMacroScopes x;
let x := { v with name := `x }.review;
IO.println $ x;
let x := addMacroScope `main x 2;
IO.println $ x;
let v := extractMacroScopes x;
let x := { v with name := `y }.review;
IO.println $ x;
let v := extractMacroScopes x;
let x := { v with name := `x }.review;
IO.println $ x;
let x := addMacroScope `main x 3;
IO.println $ x;
let x := addMacroScope `foo x 4;
IO.println $ x;
let x := addMacroScope `foo x 5;
let v := extractMacroScopes x;
check (v.mainModule == `foo);
IO.println $ x;
let x := addMacroScope `bla.bla x 6;
IO.println $ x;
let v := extractMacroScopes x;
check (v.mainModule == `bla.bla);
let x := addMacroScope `bla.bla x 7;
IO.println $ x;
let v := extractMacroScopes x;
let x := { v with name := `y }.review;
IO.println $ x;
let x := { v with name := `z.w }.review;
IO.println $ x;
pure ()

#eval test1
