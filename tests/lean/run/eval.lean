import Lean
/-!
# Tests of the `#eval` command
-/

set_option eval.type true

/-!
Basic values
-/
/-- info: 2 : Nat -/
#guard_msgs in #eval 2
/-- info: some 2 : Option Nat -/
#guard_msgs in #eval some 2
/-- info: [2, 3, 4] : List Nat -/
#guard_msgs in #eval [1,2,3].map (· + 1)

/-!
Deciding a proposition
-/
/-- info: true : Bool -/
#guard_msgs in #eval True

/-!
Can't evaluate proofs
-/
/-- error: cannot evaluate, proofs are not computationally relevant -/
#guard_msgs in #eval trivial

/-!
Can't evaluate types
-/
/-- error: cannot evaluate, types are not computationally relevant -/
#guard_msgs in #eval Nat


/-!
Capturing `dbg_trace` output
-/
def Nat.choose : Nat → Nat → Nat
  | _, 0 => dbg_trace "(_, 0)"; 1
  | 0, _ + 1 => dbg_trace "(0, _ + 1)"; 0
  | n + 1, k + 1 => dbg_trace "(_ + 1, _ + 1)"; choose n k + choose n (k + 1)
/--
info: (_ + 1, _ + 1)
(_ + 1, _ + 1)
(_, 0)
(0, _ + 1)
(_ + 1, _ + 1)
(0, _ + 1)
(0, _ + 1)
---
info: 1 : Nat
-/
#guard_msgs in #eval Nat.choose 2 2

/-!
Custom monad
-/

abbrev MyMonad := ReaderT Nat IO
/--
error: unable to synthesize 'MonadEval' instance to adapt
  MyMonad Nat
to 'IO' or 'Lean.Elab.Command.CommandElabM'.
-/
#guard_msgs in #eval (pure 2 : MyMonad Nat)

-- Note that there is no "this is due to..." diagonostic in this case.
/--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  MyMonad (Nat → Nat)
-/
#guard_msgs in #eval (pure id : MyMonad (Nat → _))

instance : MonadEval MyMonad IO where
  monadEval m := m.run 0

/-- info: 2 : Nat -/
#guard_msgs in #eval (pure 2 : MyMonad Nat)

-- Note that now we have a MonadEval instance, it doesn't mention MyMonad in the error.
/--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  Nat → Nat
-/
#guard_msgs in #eval (pure id : MyMonad (Nat → _))

/-!
Elaboration error, does not attempt to evaluate.
-/
/-- error: unknown identifier 'x' -/
#guard_msgs in #eval 2 + x

/-!
Defaulting to the CommandElabM monad
-/
/-- info: 2 : Nat -/
#guard_msgs in #eval do pure 2
/-- info: true : Bool -/
#guard_msgs in #eval do return (← Lean.getEnv).contains ``Lean.MessageData

/-!
Defaulting does not affect postponed elaborators.
-/
/-- info: 1 : Nat -/
#guard_msgs in #eval if True then 1 else 2

/-!
Testing that dbg_trace and logs carry over from all the major meta monads.
-/
/--
info: hi
---
info: dbg
-/
#guard_msgs in #eval show Lean.Elab.Term.TermElabM Unit from do dbg_trace "dbg"; Lean.logInfo m!"hi"
/--
info: hi
---
info: dbg
-/
#guard_msgs in #eval show Lean.MetaM Unit from do dbg_trace "dbg"; Lean.logInfo m!"hi"
/--
info: hi
---
info: dbg
-/
#guard_msgs in #eval show Lean.CoreM Unit from do dbg_trace "dbg"; Lean.logInfo m!"hi"

/-!
Testing delta deriving
-/
def Foo := List Nat
def Foo.mk (l : List Nat) : Foo := l

/-- info: [1, 2, 3] : Foo -/
#guard_msgs in #eval Foo.mk [1,2,3]

/-- info: [1, 2, 3] : Foo -/
#guard_msgs in #eval do return Foo.mk [1,2,3]

/-!
Testing auto-deriving
-/

inductive Baz
  | a | b

/-- info: Baz.a : Baz -/
#guard_msgs in #eval Baz.a

/-!
Returning after printing
-/
def returns : Lean.CoreM Nat := do
  IO.println "hi"
  return 2

/--
info: hi
---
info: 2 : Nat
-/
#guard_msgs in #eval returns

/-!
Throwing an exception after printing
-/
def throwsEx : Lean.CoreM Nat := do
  IO.println "hi"
  throwError "ex"

/--
info: hi
---
error: ex
-/
#guard_msgs in #eval throwsEx

/-!
Let rec support (issue #2374)
-/
/-- info: 37 : Nat -/
#guard_msgs in #eval
  let rec bar : Nat := 1
  37

/-- info: 120 : Nat -/
#guard_msgs in #eval
  let rec fact (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | n' + 1 => n * fact n'
  fact 5
