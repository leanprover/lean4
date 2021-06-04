import Lean

open Lean
open Lean Parser Term

declare_syntax_cat json
syntax strLit : json
syntax numLit : json
syntax "{" (Lean.Parser.ident ": " json),* "}" : json
syntax "[" json,* "]" : json

syntax "json " json : term

/- declare a micro json parser, so we can write our tests in a more legible way. -/
open Json in macro_rules
  | `(json $s:strLit) => s
  | `(json $n:numLit) => n
  | `(json { $[$ns : $js],* }) => do
    let mut fields := #[]
    for n in ns, j in js do
      fields := fields.push (← `(($(quote n.getId.getString!), json $j)))
    `(mkObj [$fields,*])
  | `(json [ $[$js],* ]) => do
    let mut fields := #[]
    for j in js do
      fields := fields.push (← `(json $j))
    `(Json.arr #[$fields,*])

def checkToJson [ToJson α] (obj : α) (rhs : Json) : MetaM Unit :=
  let lhs := (obj |> toJson).pretty 
  if lhs == rhs.pretty then
    ()
  else
    throwError "{lhs} ≟ {rhs}"

def checkRoundTrip [Repr α] [BEq α] [ToJson α] [FromJson α] (obj : α) : MetaM Unit :=
  let roundTripped := obj |> toJson |> fromJson?
  if let some roundTripped := roundTripped then
    if obj == roundTripped then
      ()
    else
      throwError "{repr obj} ≟ {repr roundTripped}"
  else
    throwError "couldn't parse: {repr obj} ≟ {obj |> toJson}"

-- set_option trace.Meta.debug true in
structure Foo where
  x : Nat
  y : String
deriving ToJson, FromJson, Repr, BEq

#eval checkToJson { x := 1, y := "bla" : Foo} (json { y : "bla", x : 1 })
#eval checkRoundTrip { x := 1, y := "bla" : Foo } 

-- set_option trace.Elab.command true 
structure WInfo where
  a : Nat
  b : Nat
deriving ToJson, FromJson, Repr, BEq

-- set_option trace.Elab.command true 
inductive E 
| W : WInfo → E
| WAlt (a b : Nat)
| X : Nat → Nat → E
| Y : Nat → E
| Z
deriving ToJson, FromJson, Repr, BEq

#eval checkToJson (E.W { a := 2, b := 3}) (json { W : { a : 2, b : 3 } })
#eval checkRoundTrip (E.W { a := 2, b := 3 })

#eval checkToJson (E.WAlt 2 3) (json { WAlt : { a : 2, b : 3 } })
#eval checkRoundTrip (E.WAlt 2 3)

#eval checkToJson (E.X 2 3) (json { X : [2, 3] })
#eval checkRoundTrip (E.X 2 3)

#eval checkToJson (E.Y 4) (json { Y : 4 })
#eval checkRoundTrip (E.Y 4)

#eval checkToJson E.Z (json "Z")
#eval checkRoundTrip E.Z
