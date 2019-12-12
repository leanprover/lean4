import Init.Lean.Elab
open Lean
open Lean.Elab


def run (input : String) (failIff : Bool := true) : MetaIO Unit :=
do env  ← MetaIO.getEnv;
   opts ← MetaIO.getOptions;
   let (env, messages) := process input env opts;
   messages.toList.forM $ fun msg => IO.println msg;
   when (failIff && messages.hasErrors) $ throw (IO.userError "errors have been found");
   when (!failIff && !messages.hasErrors) $ throw (IO.userError "there are no errors");
   pure ()

def fail (input : String) : MetaIO Unit :=
run input false

def M := IO Unit

def zero := 0
def one := 1
def two := 2
def hello : String := "hello"

def act1 : IO String :=
pure "hello"

#eval run "#check HasAdd.add"
#eval run "#check [zero, one, two]"
#eval run "#check id $ Nat.succ one"
#eval run "#check HasAdd.add one two"
#eval run "#check one + two > one ∧ True"
#eval run "#check act1 >>= IO.println"
#eval run "#check one + two == one"
#eval fail "#check one + one + hello == hello ++ one"

#eval run
"universe u universe v
 export HasToString (toString)
 section namespace foo.bla end bla end foo
 variable (p q : Prop)
 variable (_ b : _)
 variable {α : Type}
 variable {m : Type → Type}
 variable [Monad m]
 #check m
 #check Type
 #check Prop
 #check toString zero
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
