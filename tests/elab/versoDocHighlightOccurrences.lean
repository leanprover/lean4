import Lean

/-!
Checks that highlighting in Verso docstring code blocks attributes each token to the info tree
nodes of its own occurrence (#16631). Two tokens with the same text in one code block can be
different binders, a local variable and a constant, or literals of different types.
-/

open Lean Elab Command Doc

def showHl : DocHighlight → Option String
  | .var n _ ty => some s!"var {n} : {ty}"
  | .const n _ => some s!"const {n}"
  | .literal k ty? => some s!"literal {k} : {ty?}"
  | _ => none

partial def leanBlocks : Block ElabInline ElabBlock → Array Data.LeanBlock
  | .other (.custom v) bs => (v.get? Data.LeanBlock).toArray ++ bs.flatMap leanBlocks
  | .other _ bs => bs.flatMap leanBlocks
  | _ => #[]

/--
Prints the highlights of the tokens with text `tok` in the `lean` code blocks of `x`'s docstring.
-/
def printHighlights (x : Name) (tok : String) : CommandElabM Unit := do
  let some (.inr v) ← findInternalDocString? (← getEnv) x
    | throwError "no Verso docstring for {x}"
  for b in v.text.flatMap leanBlocks do
    for (s, hl?) in b.commands.code do
      if s == tok then
        if let some str := hl?.bind showHl then
          IO.println str

set_option doc.verso true

-- Binders with the same name in different commands

/--
```lean
example (x : Nat) : Nat := x
example (x : String) : String := x
```
-/
def twoCommands := 1

/--
info: var x : Nat
var x : Nat
var x : String
var x : String
-/
#guard_msgs in
#eval printHighlights ``twoCommands "x"

-- Shadowing within a single command

/--
```lean
example : Nat → Nat × (String → String) := fun (x : Nat) => (x, fun (x : String) => x)
```
-/
def shadowing := 1

/--
info: var x : Nat
var x : Nat
var x : String
var x : String
-/
#guard_msgs in
#eval printHighlights ``shadowing "x"

-- A local variable that has the name of a constant

/--
```lean
example (id : Nat) : Nat := id
example : Nat → Nat := id
```
-/
def varAndConst := 1

/--
info: var id : Nat
var id : Nat
const id
-/
#guard_msgs in
#eval printHighlights ``varAndConst "id"

-- Literals with the same text and different types

/--
```lean
example : Nat := 5
example : Int := 5
```
-/
def literals := 1

/--
info: literal num : (some Nat)
literal num : (some Int)
-/
#guard_msgs in
#eval printHighlights ``literals "5"
