import Lean

/-!
Creates an inductive data type with n constructors, and a function that does
a n-times-n nested non-overlapping match on it.
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
    for cIdx1 in [:con_count] do
      let con1 := mkQualCtor cIdx1
      for cIdx2 in [:con_count] do
        let con2 := mkQualCtor cIdx2
        let case ← `(matchAltExpr| | .$con1:ident (.$con2:ident n) =>n)
        cases := cases.push case
    let fdecl ←
        `(def $f:ident (x : $t:ident ($t:ident Nat)) : Nat :=
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

#test_gen T f 12

#time example := f.match_1.splitter
