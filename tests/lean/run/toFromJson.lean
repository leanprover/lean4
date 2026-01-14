import Lean

open Lean

declare_syntax_cat mjson
syntax str : mjson
syntax num : mjson
syntax "{" (ident ": " mjson),* "}" : mjson
syntax "[" mjson,* "]" : mjson

syntax "json " mjson : term

/- declare a micro json parser, so we can write our tests in a more legible way. -/
open Json in macro_rules
  | `(json $s:str) => pure s
  | `(json $n:num) => pure n
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
    pure ()
  else
    throwError "{lhs} ≟ {rhs}"

def checkRoundTrip [Repr α] [BEq α] [ToJson α] [FromJson α] (obj : α) : MetaM Unit := do
  let roundTripped := obj |> toJson |> fromJson?
  if let Except.ok roundTripped := roundTripped then
    if obj == roundTripped then
      pure ()
    else
      throwError "{repr obj} ≟ {repr roundTripped}"
  else
    throwError "couldn't parse: {repr obj} ≟ {obj |> toJson}"

-- set_option trace.Meta.debug true in
structure Foo where
  x : Nat
  y : String
deriving ToJson, FromJson, Repr, BEq

run_meta checkToJson { x := 1, y := "bla" : Foo} (json { y : "bla", x : 1 })
run_meta checkRoundTrip { x := 1, y := "bla" : Foo }

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
| YAlt (a : Nat)
| Z
deriving ToJson, FromJson, Repr, BEq

run_meta checkToJson (E.W { a := 2, b := 3}) (json { W : { a : 2, b : 3 } })
run_meta checkRoundTrip (E.W { a := 2, b := 3 })

run_meta checkToJson (E.WAlt 2 3) (json { WAlt : { a : 2, b : 3 } })
run_meta checkRoundTrip (E.WAlt 2 3)

run_meta checkToJson (E.X 2 3) (json { X : [2, 3] })
run_meta checkRoundTrip (E.X 2 3)

run_meta checkToJson (E.Y 4) (json { Y : 4 })
run_meta checkRoundTrip (E.Y 4)

run_meta checkToJson (E.YAlt 5) (json { YAlt : { a : 5 } })
run_meta checkRoundTrip (E.YAlt 5)

run_meta checkToJson E.Z (json "Z")
run_meta checkRoundTrip E.Z

inductive ERec
| mk : Nat → ERec
| W : ERec → ERec
deriving ToJson, FromJson, Repr, BEq

run_meta checkToJson (ERec.W (ERec.mk 6)) (json { W : { mk : 6 }})
run_meta checkRoundTrip (ERec.mk 7)
run_meta checkRoundTrip (ERec.W (ERec.mk 8))

inductive ENest
| mk : Nat → ENest
| W : (Array ENest) → ENest
deriving ToJson, FromJson, Repr, BEq

run_meta checkToJson (ENest.W #[ENest.mk 9]) (json { W : [{ mk : 9 }]})
run_meta checkRoundTrip (ENest.mk 10)
run_meta checkRoundTrip (ENest.W #[ENest.mk 11])

inductive EParam (α : Type)
| mk : α → EParam α
deriving ToJson, FromJson, Repr, BEq

run_meta checkToJson (EParam.mk 12) (json { mk : 12 })
run_meta checkToJson (EParam.mk "abcd") (json { mk : "abcd" })
run_meta checkRoundTrip (EParam.mk 13)
run_meta checkRoundTrip (EParam.mk "efgh")

structure Minus where
  «i-love-lisp» : Nat
  deriving ToJson, FromJson, Repr, DecidableEq

run_meta checkRoundTrip { «i-love-lisp» := 1 : Minus }
run_meta checkToJson { «i-love-lisp» := 1 : Minus } (json { «i-love-lisp»: 1 })

structure MinusAsk where
  «branches-ignore?» : Option (Array String)
  deriving ToJson, FromJson, Repr, DecidableEq

run_meta checkRoundTrip { «branches-ignore?» := #["master"] : MinusAsk }
run_meta checkToJson { «branches-ignore?» := #["master"] : MinusAsk } (json { «branches-ignore» : ["master"] })
