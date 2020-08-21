import Lean.Meta
open Lean
open Lean.Meta

universes u v w

abbrev M := ExceptT String $ MetaM

def testM {α} [HasBeq α] [HasToString α] (x : M α) (expected : α)  : MetaM Unit := do
r ← x;
match r with
| Except.ok a    => unless (a == expected) $ throwError ("unexpected result " ++ toString a)
| Except.error e => throwError ("FAILED: " ++ e)

@[noinline] def act1 : M Nat :=
throwThe Exception $ Exception.error Syntax.missing "Error at act1"

def g1 : M Nat :=
catchThe Exception
  (catch act1 (fun ex => pure 100))
  (fun ex => pure 200)

#eval testM g1 200

@[noinline] def act2 : M Nat :=
throw "hello world"

def g2 : M Nat :=
catchThe Exception
  (catch act2 (fun ex => pure 100))
  (fun ex => pure 200)

#eval testM g2 100

def h1 : CoreM Nat :=
pure 10

#eval h1

def h2 : MetaM Nat :=
pure 20

#eval h2
