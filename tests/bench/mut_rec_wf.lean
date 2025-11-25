import Lean

set_option Elab.async false

open Lean Elab
open Elab.Command (CommandElab CommandElabM elabCommand)
open Parser.Command
open Parser.Term

-- Create a name.
def strName (s : String) : Name := Name.anonymous |>.str s

def mkIndStr (idx : Nat) : String := s!"S{idx}"
def mkIndIdent (idx : Nat) : Ident := mkIdent <| strName <| mkIndStr idx

def mkQualCtor (indIdx : Nat) (c : String) : Ident :=
  mkIdent <| Name.anonymous |>.str (mkIndStr indIdx) |>.str c

def mkBaseCtorStr (idx : Nat) : String := s!"base{idx}"
def mkBaseCtorIdent (idx : Nat) : Ident := mkIdent <| strName <| mkBaseCtorStr idx

def mkIndCtorStr (idx : Nat) : String := s!"ind{idx}"
def mkIndCtorIdent (idx : Nat) := mkIdent <| strName <| mkIndCtorStr idx

def mkFnIdent (idx : Nat) := mkIdent <| strName s!"f{idx}"

def mkBaseCtor (dt : Ident) (cIdx : Nat): CommandElabM (TSyntax ``ctor) := do
  let base := mkBaseCtorIdent cIdx
  `(ctor| | $base:ident : $dt )

/--
`#test_gen name dt ccnt icnt` creates
`dt` mutually inductive types where each type has `ccnt` nullary constructors
and `icnt` unary recursive constructors
-/
syntax (name := testGen) (docComment)? "#test_gen" ident num num num : command -- declare the syntax

@[command_elab testGen]
def testGenImpl: CommandElab := fun stx => do
  match stx with
  | `(#test_gen $ns:ident $datatype_count $base_count $ind_count) =>
    let datatype_count := datatype_count.getNat
    let base_count := base_count.getNat
    let ind_count := ind_count.getNat
    let mkInd (dtIdx : Nat) : CommandElabM Command := do
      let indName := mkIndIdent dtIdx
      let dt := mkIndIdent dtIdx
      -- Create constant case definitions
      let baseCases ← Array.ofFnM (n := base_count) fun cIdx =>
        let base := mkBaseCtorIdent cIdx
        `(ctor| | $base:ident : $dt )
      let indCases ← Array.ofFnM (n := ind_count) fun cIdx =>
        let base := mkIndCtorIdent cIdx.val
        let ind := mkIndIdent ((dtIdx + cIdx.val) % datatype_count)
        `(ctor| | $base:ident : $ind -> $dt )
      `(inductive $indName where
        $baseCases:ctor*
        $indCases:ctor*
      )
    let decls ← Array.ofFnM (n := datatype_count) fun i => mkInd i.val
    elabCommand =<< `(
      namespace $ns
      mutual
      $decls:command*
      end
      end $ns)
    let mkRec (dtIdx : Nat) : CommandElabM Command := do
      let recName := mkFnIdent dtIdx
      let indName := mkIndIdent dtIdx
      let baseCases ← Array.ofFnM (n := base_count) fun cIdx =>
        let base := mkQualCtor dtIdx (mkBaseCtorStr cIdx.val)
        `(matchAltExpr| | $base:ident => $base )
      let indCases ← Array.ofFnM (n := ind_count) fun cIdx =>
        let ctor := mkQualCtor dtIdx (mkIndCtorStr cIdx.val)
        let fi :=   mkFnIdent ((dtIdx + cIdx.val) % datatype_count)
        `(matchAltExpr| | $ctor:ident i => $ctor ($fi i))
      if ind_count > 0 then
        `(def $recName (x : $indName) : $indName :=
            match x with
            $baseCases:matchAlt*
            $indCases:matchAlt*
          termination_by sizeOf x
        )
      else
        `(def $recName (x : $indName) : $indName :=
            match x with
            $baseCases:matchAlt*
            $indCases:matchAlt*
        )
    let decls ← Array.ofFnM (n := datatype_count) fun i => mkRec i.val
    elabCommand =<< `(
      namespace $ns
      mutual
      $decls:command*
      end
      end $ns)

  | _ =>
    throwIllFormedSyntax


-- set_option trace.profiler true
-- set_option trace.profiler.threshold 5
-- set_option trace.profiler.output "profiler.out"
-- set_option trace.profiler.useHeartbeats true
set_option profiler true
-- set_option profiler.threshold 10
-- set_option trace.Elab.definition.wf.eqns true
-- set_option trace.Meta.Match.matchEqs true

/-
Expanding number of constants increases time quadraticly.
#test_gen C 2 40 1
#test_gen D 2 80 1
-/

-- Expanding number of indutive cases seems fairly quick until a typing point is reached.

-- #test_gen A 1 1 4
--#test_gen B 2 1 2
--#test_gen C 2 1 4
--#test_gen D 2 1 8
--#test_gen E 2 1 16

-- There is a big change with the change from 32 to 64.

-- #test_gen F 2 1 32

-- ..
-- simp took 172ms
-- process pre-definitions took 408ms
--  elaboration took 268ms

#test_gen G 2 1 64


-- .. many more simp calls appearing than 32
--  process pre-definitions took 1.97s
--  elaboration took 5.47s

-- On nightly-07-16, this triggers an internal error but it could not be reproduced on live (due to timeout).
--   Lean.Environment:464:4: duplicate normalized declaration name H.f0 vs. H.f0
--#test_gen H 2 1 128
