import Lean

/-!
Creates an non-recursive inductive data type with n constructors and deriving `BEq`.
-/

set_option Elab.async false

open Lean Elab
open Elab.Command (CommandElab CommandElabM elabCommand)
open Parser.Command
open Parser.Term

-- Create a name.
def strName (s : String) : Name := Name.anonymous |>.str s
def mkCtorStr (idx : Nat) : String := s!"con{idx}"
def mkCtorIdent (idx : Nat) : Ident := mkIdent <| strName <| mkCtorStr idx

/--
`#test_gen name cnt` creates an inductive type with icnt` unary constructors
-/
syntax (name := testGen) (docComment)? "#test_gen" ident num : command -- declare the syntax

@[command_elab testGen]
def testGenImpl: CommandElab := fun stx => do
  match stx with
  | `(#test_gen $t $con_count) =>
    let con_count := con_count.getNat
    let cons ← Array.ofFnM (n := con_count) fun cIdx =>
      let con := mkCtorIdent cIdx
      `(ctor| | $con:ident : α → $t:ident α )
    let idecl ←
      -- Create constant case definitions
      `(inductive $t:ident (α : Type) : Type where
        $cons:ctor*
        deriving DecidableEq
      )
    elabCommand idecl
  | _ =>
    throwIllFormedSyntax

#time #test_gen T 30
