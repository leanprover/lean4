import Init.Lean.Elab
open Lean
open Lean.Elab

def run (input : String) (failIff : Bool := true) : MetaIO Unit :=
do env  ← MetaIO.getEnv;
   opts ← MetaIO.getOptions;
   (env, messages) ← liftM $ process input env opts;
   messages.forM $ fun msg => IO.println msg;
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

#eval run "#check @HasAdd.add"
#eval run "#check [zero, one, two]"
#eval run "#check id $ Nat.succ one"
#eval run "#check HasAdd.add one two"
#eval run "#check one + two > one ∧ True"
#eval run "#check act1 >>= IO.println"
#eval run "#check one + two == one"
#eval fail "#check one + one + hello == hello ++ one"
#eval run "#check Nat.add one $ Nat.add one two"

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

structure S1 :=
(x y : Nat := 0)

structure S2 extends S1 :=
(z : Nat := 0)

def fD {α} [HasToString α] (a b : α) : String :=
toString a ++ toString b

structure S3 :=
(w : Nat := 0)
(f : forall {α : Type} [HasToString α], α → α → String := @fD)

structure S4 extends S2, S3 :=
(s : Nat := 0)

def s4 : S4 := {}

structure S (α : Type) :=
(field1 : S4 := {})
(field2 : S4 × S4 := ({}, {}))
(field3 : α)
(field4 : List α × Nat := ([], 0))
(vec : Array (α × α) := #[])
(map : HashMap String α := {})

inductive D (α : Type)
| mk (a : α) (s : S4) : D

def s : S Nat := { field3 := 0 }
def d : D Nat := D.mk 10 {}
def i : Nat := 10
def k : String := "hello"

universes u

class Monoid (α : Type u) :=
(one {} : α)
(mul    : α → α → α)

def m : Monoid Nat :=
{ one := 1, mul := Nat.mul }

def f (x y z : Nat) : Nat :=
x + y + z

#eval run "#check s4.x"
#eval run "#check s.field1.x"
#eval run "#check s.field2.fst"
#eval run "#check s.field2.fst.w"
#eval run "#check s.1.x"
#eval run "#check s.2.1.x"
#eval run "#check d.1"
#eval run "#check d.2.x"
#eval run "#check s4.f s4.x"
#eval run "#check m.mul m.one"
#eval run "#check s.field4.1.length.succ"
#eval run "#check s.field4.1.map Nat.succ"
#eval run "#check s.vec[i].1"
#eval run "#check \"hello\""
#eval run "#check 1"
#eval run "#check Nat.succ 1"
#eval run "#check fun _ a (x y : Int) => x + y + a"
#eval run "#check (one)"
#eval run "#check ()"
#eval run "#check (one, two, zero)"
#eval run "#check (one, two, zero)"
#eval run "#check (1 : Int)"
#eval run "#check ((1, 2) : Nat × Int)"
#eval run "#check (· + one)"
#eval run "#check (· + · : Nat → Nat → Nat)"
#eval run "#check (f one · zero)"
#eval run "#check (f · · zero)"
#eval run "#check fun (_ b : Nat) => b + 1"

def foo {α β} (a : α) (b : β) (a' : α) : α :=
a

def bla {α β} (f : α → β) (a : α) : β :=
f a

-- #check fun x => foo x x.w s4 -- fails in old elaborator
-- #check bla (fun x => x.w) s4 -- fails in the old elaborator
-- #check #[1, 2, 3].foldl (fun r a => r.push a) #[] -- fails in the old elaborator

#eval run "#check fun x => foo x x.w s4"
#eval run "#check bla (fun x => x.w) s4"
#eval run "#check #[1, 2, 3].foldl (fun r a => r.push a) #[]"
#eval run "#check #[1, 2, 3].foldl (fun r a => (r.push a).push a) #[]"
#eval run "#check #[1, 2, 3].foldl (fun r a => ((r.push a).push a).push a) #[]"
#eval run "#check #[].push one $.push two $.push zero $.size.succ"
#eval run "#check #[1, 2].foldl (fun r a => r.push a $.push a $.push a) #[]"
#eval run "#check #[1, 2].foldl (init := #[]) $ fun r a => r.push a $.push a"


#eval run "#check let x := one + zero; x + x"
-- set_option trace.Elab true
#eval run "#check (fun x => let v := x.w; v + v) s4"
#eval run "#check fun x => foo x (let v := x.w; v + one) s4"
#eval run "#check fun x => foo x (let v := x.w; let w := x.x; v + w + one) s4"
#eval fail "#check id.{1,1}"
#eval fail "#check @id.{0} Nat"
#eval run "#check @id.{1} Nat"
#eval run "universes u #check id.{u}"
#eval fail "universes u #check id.{v}"
#eval run "universes u #check Type u"
#eval run "universes u #check Sort u"
#eval run "#check Type 1"
#eval run "#check Type 0"
#eval run "universes u v #check Sort (max u v)"
#eval run "universes u v #check Type (max u v)"
#eval run "#check 'a'"
#eval fail "#check #['a', \"hello\"]"
#eval run "#check fun (a : Array Nat) => a.size"
#eval run "#check if 0 = 1 then 'a' else 'b'"
#eval run "#check fun (i : Nat) (a : Array Nat) => if h : i < a.size then a.get (Fin.mk i h) else i"
#eval run "#check { x : Nat // x > 0 }"
#eval run "#check { x // x > 0 }"
#eval run "#check fun (i : Nat) (a : Array Nat) => if h : i < a.size then a.get ⟨i, h⟩ else i"
#eval run "#check Prod.fst ⟨1, 2⟩"
#eval run "#check let x := ⟨1, 2⟩; Prod.fst x"
#eval run "#check show Nat from 1"
#eval run "#check show Int from 1"
#eval run "#check have Nat from one + zero; this + this"
#eval run "#check have x : Nat from one + zero; x + x"
#eval run "#check have Nat := one + zero; this + this"
#eval run "#check have x : Nat := one + zero; x + x"
#eval run "#check x + y where x := 1; where y := x + x"
#eval run "#check let z := 2; x + y where x := z + 1; where y := x + x"

#eval run "variables {α β} axiom x (n : Nat) : α → α #check x 1 0"
#eval run "#check HasToString.toString 0"
#eval run "@[instance] axiom newInst : HasToString Nat #check newInst #check HasToString.toString 0"
#eval run "variables {β σ} universes w1 w2 /-- Testing axiom -/ unsafe axiom Nat.aux.{u, v} (γ : Type w1) (v : Nat) : β → (α : Type _) → v = zero /- Nat.zero -/ → Array α #check @Nat.aux"
#eval run "def x : Nat := Nat.zero #check x"
#eval run "def x := Nat.zero #check x"
#eval run "open Lean.Parser def x := parser! symbol \"foo\" Nat.zero #check x"
#eval run "open Lean.Parser def x := tparser! symbol \"foo\" Nat.zero #check x"
#eval run "def x : Nat := 1 #check x"
