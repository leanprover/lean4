import Lean.Meta

open Lean
open Lean.Meta

universe u v w

abbrev M := ExceptT String MetaM

def testM {α} [BEq α] [ToString α] (x : M α) (expected : α)  : MetaM Unit := do
  let r ← x
  match r with
  | Except.ok a    => unless a == expected do throwError m!"unexpected result {a}"
  | Except.error e => throwError m!"FAILED: {e}"

@[noinline] def act1 : M Nat :=
  throw <| Exception.error Syntax.missing "Error at act1"

def g1 : M Nat :=
  tryCatchThe Exception
    (tryCatchThe String act1 (fun ex => pure 100))
    (fun ex => pure 200)

#guard_msgs in
#eval testM g1 200

@[noinline] def act2 : M Nat :=
  throwThe String "hello world"

def g2 : M Nat :=
tryCatchThe Exception
  (tryCatchThe String act2 (fun ex => pure 100))
  (fun ex => pure 200)

#guard_msgs in
#eval testM g2 100

def h1 : CoreM Nat :=
pure 10

/-- info: 10 -/
#guard_msgs in
#eval h1

def h2 : MetaM Nat :=
pure 20

/-- info: 20 -/
#guard_msgs in
#eval h2
