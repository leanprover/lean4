import Lean

/-!
Creates a match on nat literals with a catch-all case.
-/

set_option Elab.async false

open Lean Elab
open Elab.Command (CommandElab CommandElabM elabCommand)
open Parser.Command
open Parser.Term

-- Create a name.
def strName (s : String) : Name := Name.anonymous |>.str s

def mkBaseCtorStr (idx : Nat) : String := s!"base{idx}"
def mkBaseCtorIdent (idx : Nat) : Ident :=
  mkIdent <| strName <| mkBaseCtorStr idx
def mkQualCtor (idx : Nat) : Ident :=
  mkIdent <| Name.anonymous |>.str (mkBaseCtorStr idx)

/--
`#test_gen name dt ccnt icnt` creates
`dt` mutually inductive types where each type has `ccnt` nullary constructors
and `icnt` unary recursive constructors
-/
syntax (name := testGen) (docComment)? "#test_gen" ident num : command -- declare the syntax

@[command_elab testGen]
def testGenImpl: CommandElab := fun stx => do
  match stx with
  | `(#test_gen $f $n) =>
    let n := n.getNat
    -- Generate some non-continugious numbers
    let mut ms := #[]
    let mut j := 0
    for _ in [:n] do
      ms := ms.push (ms.size + j)
      j := j + ms.size
    let cases ← ms.mapIdxM fun i m =>
      `(matchAltExpr| | $(Syntax.mkNatLit m) => $(Syntax.mkNatLit i))
    let cases := cases.push (← `(matchAltExpr| | _ => $(Syntax.mkNatLit n)))
    let stx ←
        `(def $f:ident : Nat → Nat
            $cases:matchAlt*
        )
    -- logInfo stx
    elabCommand stx
  | _ =>
    throwIllFormedSyntax

#time #test_gen f 200

-- #time example := f.match_1.splitter
