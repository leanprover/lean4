import Lean

/-!
Creates an inductive data type with n constructors, and a function that does
matches on half of its constructors, with a catch-all for the other hal.
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
syntax (name := testGen) (docComment)? "#test_gen" ident ident num : command -- declare the syntax

@[command_elab testGen]
def testGenImpl: CommandElab := fun stx => do
  match stx with
  | `(#test_gen $t $f $con_count) =>
    let con_count := con_count.getNat
    let cons ← Array.ofFnM (n := con_count) fun cIdx =>
      let con := mkBaseCtorIdent cIdx
      `(ctor| | $con:ident : α → $t:ident α )
    let idecl ←
      -- Create constant case definitions
      `(inductive $t:ident α where
        $cons:ctor*
      )
    let mut cases : TSyntaxArray `Lean.Parser.Term.matchAlt := #[]
    for cIdx1 in [:con_count/2] do
      let con1 := mkQualCtor cIdx1
      let case ← `(matchAltExpr| | .$con1:ident n =>n)
      cases := cases.push case
    cases := cases.push (← `(matchAltExpr| | _ => 0))
    let fdecl ←
        `(def $f:ident (x : $t:ident Nat) : Nat :=
            match x with
            $cases:matchAlt*
        )
    let stx ← `(
      $idecl:command
      $fdecl:command
      )
    -- logInfo stx
    elabCommand stx
  | _ =>
    throwIllFormedSyntax

#test_gen T f 100

#time example := f.match_1.splitter
