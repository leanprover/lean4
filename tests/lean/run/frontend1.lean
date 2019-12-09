import Init.Lean.Elab
open Lean
open Lean.Elab

def run (input : String) : MetaIO Unit :=
do opts ← MetaIO.getOptions;
   (env, messages) ← liftM $ testFrontend input opts;
   messages.toList.forM $ fun msg => IO.println msg;
   pure ()

set_option trace.Elab true

#eval run
"import Init.Core
 universe u universe v
 section namespace foo.bla end bla end foo
 variable (p q : Prop)
 variable (_ b : _)
 variable {α : Type}
 -- variable [Monad m]
 #check Type
 #check Prop
 #check p
 #check α
 #check Nat.succ
 #check Nat.add
 end"
