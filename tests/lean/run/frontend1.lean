import Init.Lean.Elab
open Lean
open Lean.Elab


def run (input : String) : MetaIO Unit :=
do env  ← MetaIO.getEnv;
   opts ← MetaIO.getOptions;
   let (env, messages) := process input env opts;
   messages.toList.forM $ fun msg => IO.println msg;
   when messages.hasErrors $ throw (IO.userError "errors have been found");
   pure ()

def M := IO Unit

def zero := 0
def one := 1
def two := 2
-- set_option trace.Elab.app true
-- set_option trace.Elab true

#eval run "#check [zero, one, two]"
#eval run "#check id $ Nat.succ one"
#eval run "#check HasAdd.add one two"

#eval run
"universe u universe v
 section namespace foo.bla end bla end foo
 variable (p q : Prop)
 variable (_ b : _)
 variable {α : Type}
 variable {m : Type → Type}
 variable [Monad m]
 #check m
 #check Type
 #check Prop
 #check id Nat.zero (α := Nat)
 #check id _ (α := Nat)
 #check id Nat.zero
 #check id (α := Nat)
 #check @id Nat
 #check p
 #check α
 #check Nat.succ
 #check Nat.add
 #check id
 #check forall (α : Type), α → α
 #check (α : Type) → α → α
 #check {α : Type} → {β : Type} → M → (α → β) → α → β
 #check ()
 #check run
 end"
