#lang lean4
import Lean.Elab
open Lean
open Lean.Elab

def runM (input : String) (failIff : Bool := true) : CoreM Unit := do
let env  ← getEnv;
let opts ← getOptions;
let (env, messages) ← liftIO $ process input env opts;
messages.forM $ fun msg => (liftIO msg.toString) >>= IO.println;
when (failIff && messages.hasErrors) $ throwError "errors have been found";
when (!failIff && !messages.hasErrors) $ throwError "there are no errors";
pure ()

def fail (input : String) : CoreM Unit :=
runM input false

def M := IO Unit

def zero := 0
def one := 1
def two := 2
def hello : String := "hello"

def act1 : IO String :=
pure "hello"

#eval runM "#check @HasAdd.add"
#eval runM "#check [zero, one, two]"
#eval runM "#check id $ Nat.succ one"
#eval runM "#check HasAdd.add one two"
#eval runM "#check one + two > one ∧ True"
#eval runM "#check act1 >>= IO.println"
#eval runM "#check one + two == one"
#eval fail "#check one + one + hello == hello ++ one"
#eval runM "#check Nat.add one $ Nat.add one two"

#eval runM
"universe u universe v
 export ToString (toString)
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
 end"

structure S1 :=
(x y : Nat := 0)

structure S2 extends S1 :=
(z : Nat := 0)

def fD {α} [ToString α] (a b : α) : String :=
toString a ++ toString b

structure S3 :=
(w : Nat := 0)
(f : forall {α : Type} [ToString α], α → α → String := @fD)

structure S4 extends S2, S3 :=
(s : Nat := 0)

def s4 : S4 := {}

structure S (α : Type) :=
(field1 : S4 := {})
(field2 : S4 × S4 := ({}, {}))
(field3 : α)
(field4 : List α × Nat := ([], 0))
(vec : Array (α × α) := #[])
(map : Std.HashMap String α := {})

inductive D (α : Type)
| mk (a : α) (s : S4) : D α

def s : S Nat := { field3 := 0 }
def d : D Nat := D.mk 10 {}
def i : Nat := 10
def k : String := "hello"

universes u

class Monoid (α : Type u) :=
(one : α)
(mul : α → α → α)

def m : Monoid Nat :=
{ one := 1, mul := Nat.mul }

def f (x y z : Nat) : Nat :=
x + y + z

#eval runM "#check s4.x"
#eval runM "#check s.field1.x"
#eval runM "#check s.field2.fst"
#eval runM "#check s.field2.fst.w"
#eval runM "#check s.1.x"
#eval runM "#check s.2.1.x"
#eval runM "#check d.1"
#eval runM "#check d.2.x"
#eval runM "#check s4.f s4.x"
#eval runM "#check m.mul m.one"
#eval runM "#check s.field4.1.length.succ"
#eval runM "#check s.field4.1.map Nat.succ"
#eval runM "#check s.vec[i].1"
#eval runM "#check \"hello\""
#eval runM "#check 1"
#eval runM "#check Nat.succ 1"
#eval runM "#check fun _ a (x y : Int) => x + y + a"
#eval runM "#check (one)"
#eval runM "#check ()"
#eval runM "#check (one, two, zero)"
#eval runM "#check (one, two, zero)"
#eval runM "#check (1 : Int)"
#eval runM "#check ((1, 2) : Nat × Int)"
#eval runM "#check (· + one)"
#eval runM "#check (· + · : Nat → Nat → Nat)"
#eval runM "#check (f one · zero)"
#eval runM "#check (f · · zero)"
#eval runM "#check fun (_ b : Nat) => b + 1"

def foo {α β} (a : α) (b : β) (a' : α) : α :=
a

def bla {α β} (f : α → β) (a : α) : β :=
f a

-- #check fun x => foo x x.w s4 -- fails in old elaborator
-- #check bla (fun x => x.w) s4 -- fails in the old elaborator
-- #check #[1, 2, 3].foldl (fun r a => r.push a) #[] -- fails in the old elaborator

#eval runM "#check fun x => foo x x.w s4"
#eval runM "#check bla (fun x => x.w) s4"
#eval runM "#check #[1, 2, 3].foldl (fun r a => r.push a) #[]"
#eval runM "#check #[1, 2, 3].foldl (fun r a => (r.push a).push a) #[]"
#eval runM "#check #[1, 2, 3].foldl (fun r a => ((r.push a).push a).push a) #[]"
#eval runM "#check #[].push one $.push two $.push zero $.size.succ"
#eval runM "#check #[1, 2].foldl (fun r a => r.push a $.push a $.push a) #[]"
#eval runM "#check #[1, 2].foldl (init := #[]) $ fun r a => r.push a $.push a"

#eval runM "#check let x := one + zero; x + x"
-- set_option trace.Elab true
#eval runM "#check (fun x => let v := x.w; v + v) s4"
#eval runM "#check fun x => foo x (let v := x.w; v + one) s4"
#eval runM "#check fun x => foo x (let v := x.w; let w := x.x; v + w + one) s4"
#eval fail "#check id.{1,1}"
#eval fail "#check @id.{0} Nat"
#eval runM "#check @id.{1} Nat"
#eval runM "universes u #check id.{u}"
#eval fail "universes u #check id.{v}"
#eval runM "universes u #check Type u"
#eval runM "universes u #check Sort u"
#eval runM "#check Type 1"
#eval runM "#check Type 0"
#eval runM "universes u v #check Sort (max u v)"
#eval runM "universes u v #check Type (max u v)"
#eval runM "#check 'a'"
#eval fail "#check #['a', \"hello\"]"
#eval runM "#check fun (a : Array Nat) => a.size"
#eval runM "#check if 0 = 1 then 'a' else 'b'"
#eval runM "#check fun (i : Nat) (a : Array Nat) => if h : i < a.size then a.get (Fin.mk i h) else i"
#eval runM "#check { x : Nat // x > 0 }"
#eval runM "#check { x // x > 0 }"
#eval runM "#check fun (i : Nat) (a : Array Nat) => if h : i < a.size then a.get ⟨i, h⟩ else i"
#eval runM "#check Prod.fst ⟨1, 2⟩"
#eval runM "#check let x := ⟨1, 2⟩; Prod.fst x"
#eval runM "#check show Nat from 1"
#eval runM "#check show Int from 1"
#eval runM "#check have Nat from one + zero; this + this"
#eval runM "#check have x : Nat from one + zero; x + x"
#eval runM "#check have Nat := one + zero; this + this"
#eval runM "#check have x : Nat := one + zero; x + x"
#eval runM "#check x + y where x := 1; where y := x + x"
#eval runM "#check let z := 2; x + y where x := z + 1; where y := x + x"

#eval runM "variables {α β} axiom x (n : Nat) : α → α #check x 1 0"
#eval runM "#check ToString.toString 0"
#eval runM "@[instance] axiom newInst : ToString Nat #check newInst #check ToString.toString 0"
#eval runM "variables {β σ} universes w1 w2 /-- Testing axiom -/ unsafe axiom Nat.aux (γ : Type w1) (v : Nat) : β → (α : Type _) → v = zero /- Nat.zero -/ → Array α #check @Nat.aux"
#eval runM "def x : Nat := Nat.zero #check x"
#eval runM "def x := Nat.zero #check x"
#eval runM "open Lean.Parser def x := parser! symbol \"foo\" #check x"
#eval runM "open Lean.Parser def x := parser!:50 symbol \"foo\" #check x"
#eval runM "open Lean.Parser def x := tparser! symbol \"foo\" #check x"
#eval runM "def x : Nat := 1 #check x"


def g (x : Nat := zero) (y : Nat := one) (z : Nat := two) : Nat :=
x + y + z

def three := 3

#eval runM "#check g"
#eval runM "#check g (x := three) (z := zero)"
#eval runM "#check g (y := three)"
#eval runM "#check g (z := three)"
#eval runM "#check g three (z := zero)"

#eval runM "#check (fun stx => if True then let e := stx; HasPure.pure e else HasPure.pure stx : Nat → Id Nat)"
#eval runM "constant n : Nat #check n"

#eval fail "#check Nat.succ 'a'"

#eval runM "universes u v #check Type (max u v)"
#eval runM "universes u v #check Type (imax u v)"

#eval fail "namespace Boo def f (x : Nat) := x def s := 'a' #check (fun x => f x) s end Boo"
