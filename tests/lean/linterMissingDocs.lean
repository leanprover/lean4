import Lean

set_option linter.all true

/-- A doc string -/
def hasDoc (x : Nat) := x

def noDoc (x : Nat) := x

private def auxDef (x : Nat) := x

namespace Foo
protected def noDoc2 (x : Nat) := x
end Foo

open Foo in
def openIn (x : Nat) := x

open Foo in
/-- A doc string -/
def openIn2 (x : Nat) := x

set_option pp.all true in
def setOptionIn1 (x : Nat) := x

set_option pp.all true in
/-- A doc string -/
def setOptionIn2 (x : Nat) := x

set_option linter.all false in
def nolintAll (x : Nat) := x

set_option linter.all true in
set_option linter.missingDocs false in
def nolintDoc (x : Nat) := x

set_option linter.all false in
set_option linter.missingDocs true in
def lintDoc (x : Nat) := x

inductive Ind where
  | ind1
  | ind2 : Ind → Ind
  | /-- A doc string -/ doc : Ind
with
  @[computedField] field : Ind → Nat
  | _ => 1

structure Foo where
  mk1 : Nat
  /-- test -/
  (mk2 mk3 : Nat)
  {mk4 mk5 : Nat}
  [mk6 mk7 : Nat]

class Bar (α : Prop) := mk ::

theorem aThm : True := trivial
example : True := trivial
instance : Bar True := ⟨⟩

initialize init : Unit ← return
initialize return

declare_syntax_cat myCat

syntax "my_syn" : myCat
syntax (name := namedSyn) "my_named_syn" myCat : command

macro_rules | `(my_named_syn my_syn) => `(def hygienic := 1)
elab_rules : command | `(my_named_syn my_syn) => return

my_named_syn my_syn

elab "my_elab" : term => return Lean.mkConst ``false
macro "my_macro" : term => `(my_elab)

class abbrev BarAbbrev (α : Prop) := Bar α

register_option myOption : Bool := { defValue := my_macro, descr := "hi mom" }
