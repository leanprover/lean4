import Lean
set_option autoImplicit false

namespace Foo.Bar
abbrev Bar := Nat
end Foo.Bar

open Foo Bar in
def myNat1 : Bar := 10 -- good

namespace Bar
end Bar

open Foo Bar in
def myNat2 : Bar := 10

open Foo.Bar in
def myNat3 : Bar := 10 -- good

open Foo Bar in
def myNat4 : Bar.Bar := 10 -- good

section
open Lean Parser Elab Tactic

/-- info: Lean.Parser.Tactic.rwRule : ParserDescr -/
#guard_msgs in
#check rwRule

/-- info: Lean.Elab.Tactic.evalDSimp : Tactic -/
#guard_msgs in
#check evalDSimp
end

section
open Lean

/-- info: Lean.Parser.Tactic.rwRule : ParserDescr -/
#guard_msgs in
#check Parser.Tactic.rwRule

open Parser

/-- info: Lean.Parser.Tactic.rwRule : ParserDescr -/
#guard_msgs in
#check Tactic.rwRule

end
