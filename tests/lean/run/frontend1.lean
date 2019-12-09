import Init.Lean.Elab
open Lean
open Lean.Elab

def run (input : String) : IO Unit :=
do (env, messages) ← testFrontend input;
   messages.toList.forM $ fun msg => IO.println msg;
   pure ()

#eval run
"import Init.Core
 universe u universe v
 section namespace foo.bla end bla end foo
 variable (p q : Prop)
 variable (_ b : _)
 variable {α : Type}
 -- variable [Monad m]
 end"
