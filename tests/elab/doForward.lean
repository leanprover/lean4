/-!
Behavioural tests for `do←`, the effect-forwarding marker that lets ordinary
continuation-taking wrappers (`withReader`, `withFinalizer`, …) participate
in the surrounding `do` block's control flow.
-/

set_option backward.do.legacy false

namespace DoForwardTest

/-! ### Effect forwarding -/

/-- A wrapper that runs `fin` after the body. -/
def withFinalizer [Monad m] (fin : m Unit) (body : m α) : m α := do
  let r ← body; fin; return r

-- `mut`-variable reassignment in the forwarded body persists after the wrapper.
/-- info: 5 -/
#guard_msgs in
#eval show IO Nat from do
  let mut x := 0
  withFinalizer (pure ()) (do← x := x + 5)
  return x

/-- A continuation-taking wrapper that invokes `k` with `x`. -/
def withInjected [Monad m] (x : α) (k : α → m β) : m β := do
  k x

-- The forwarded body sees the continuation's parameter and the outer mut state.
/-- info: 14 -/
#guard_msgs in
#eval show IO Nat from do
  let mut x := 0
  withInjected 7 (fun y => do← x := y * 2)
  return x

-- Early `return` from the forwarded body short-circuits the outer `do`.
/-- info: 42 -/
#guard_msgs in
#eval show IO Nat from do
  withFinalizer (pure ()) (do← return 42)
  return 0

-- `break` from the forwarded body targets the outer `for`.
/-- info: 6 -/
#guard_msgs in
#eval show IO Nat from do
  let mut total := 0
  for i in [1, 2, 3, 4, 5] do
    withInjected i (fun y => do←
      if y > 3 then break
      total := total + y)
  return total

-- `continue` from the forwarded body targets the outer `for`.
/-- info: 9 -/
#guard_msgs in
#eval show IO Nat from do
  let mut total := 0
  for i in [1, 2, 3, 4, 5] do
    withInjected i (fun y => do←
      if y % 2 = 0 then continue
      total := total + y)
  return total

/-! ### Syntax variants -/

-- ASCII `do<-` is accepted in place of `do←`.
/-- info: 11 -/
#guard_msgs in
#eval show IO Nat from do
  let mut x := 0
  withFinalizer (pure ()) (do<- x := x + 11)
  return x

-- Whitespace between `do` and the arrow is rejected: `do <-` parses as
-- `do (← …)` (the existing `«do»` + nested-action combo) and fails to type-check here.
/-- has type
  Unit
but is expected to have type
  IO Unit -/
#guard_msgs (substring := true) in
example : IO Unit := do
  withFinalizer (pure ()) (do <- pure ())
  pure ()

-- `do←` outside a function-application context is rejected.
/--
error: `do←` may only appear as the last argument of a function application inside an enclosing `do` block, optionally inside a `fun` binder
-/
#guard_msgs in
example : IO Unit := do← pure ()

/-! ### Argument routing -/

/-- Wrapper with body first, trailing optional. -/
def withOptFin [Monad m] (body : m α) (fin : m Unit := pure ()) : m α := do
  let r ← body; fin; return r

-- Trailing optional defaulted; the forwarded body is the only positional arg.
/-- info: 5 -/
#guard_msgs in
#eval show IO Nat from do
  let mut x := 0
  withOptFin (do← x := x + 5)
  return x

-- Trailing optional supplied via named arg before the body; body is still syntactic-last.
/-- info: 7 -/
#guard_msgs in
#eval show IO Nat from do
  let mut x := 0
  withOptFin (fin := pure ()) (do← x := x + 7)
  return x

/-- Wrapper with body first, then a non-default explicit arg. -/
def withBodyFirst [Monad m] (body : m α) (cfg : Bool) : m α := do
  let r ← body
  if cfg then pure () else pure ()
  return r

-- Named arg routes around the second explicit position, leaving the body as
-- the syntactic last positional argument even though it binds to the *first*
-- signature slot.
/-- info: 20 -/
#guard_msgs in
#eval show IO Nat from do
  let mut x := 0
  withBodyFirst (cfg := true) (do← x := x + 20)
  return x

-- Negative: forwarded body followed by a named arg is no longer syntactic-last.
/--
error: `do←` may only appear as the last argument of a function application inside an enclosing `do` block, optionally inside a `fun` binder
-/
#guard_msgs in
example : IO Unit := do
  let mut x := 0
  withOptFin (do← x := x + 3) (fin := pure ())

/-! ### Wrapper validation

The wrapper's signature must shape up to `(… → m α) → m α` for some `α` that is universally
quantified in the wrapper's signature and appears nowhere else. -/

-- Wrapper returns `m Unit` regardless of the body's `α`.
def withDiscard [Pure m] (_body : m α) : m Unit := pure ()

/-- is not a valid `do←` wrapper -/
#guard_msgs (substring := true) in
example : IO Nat := do
  withDiscard (do← return 99)
  return 1

-- `α` appears in a non-forwarded explicit argument.
def withConst [Pure m] (a : m α) (_b : m α) : m α := a

/-- is not a valid `do←` wrapper -/
#guard_msgs (substring := true) in
example : IO Nat := do
  withConst (return ()) (do← return 99)
  return 1

-- `α` is fixed to `Bool`, not universally quantified.
def withFixed [Monad m] (k : Nat → m Bool) : m Bool := k 5

/-- is not a valid `do←` wrapper -/
#guard_msgs (substring := true) in
example : IO Bool := do
  let mut x := 0
  withFixed fun n => do←
    x := x + n
    return true

-- Wrapper returns `m (α × α)` rather than `m α`.
def withDoubled [Monad m] (k : Nat → m α) : m (α × α) := do
  let x ← k 1; let y ← k 2; return (x, y)

/-- is not a valid `do←` wrapper -/
#guard_msgs (substring := true) in
example : IO (Nat × Nat) := do
  let mut sum := 0
  withDoubled fun n => do←
    sum := sum + n
    return n

-- `foldlM` threads its `β` through both `init` and the accumulator argument
-- of the body, so the result type variable is not free for forwarding.
/-- is not a valid `do←` wrapper -/
#guard_msgs (substring := true) in
example : IO Nat := do
  let mut total := 0
  let _ ← #[1,2,3].foldlM (init := 0) fun acc n => do←
    total := total + n
    return acc + n
  return total

/-! ### Binder types

The binders of a forwarded body take their types from the wrapper's body slot. -/

-- Field notation on a binder resolves.
/-- info: 3 -/
#guard_msgs in
#eval show IO Nat from do
  let mut n := 0
  withInjected #[1, 2, 3] (fun as => do← n := as.size)
  return n

-- An ascribed binder is accepted.
/-- info: 3 -/
#guard_msgs in
#eval show IO Nat from do
  let mut n := 0
  withInjected #[1, 2, 3] (fun (as : Array Nat) => do← n := as.size)
  return n

/-- A wrapper that invokes `k` with two arguments. -/
def withInjected2 [Monad m] (x : α) (y : β) (k : α → β → m γ) : m γ := k x y

-- Every binder takes its type from the wrapper.
/-- info: 5 -/
#guard_msgs in
#eval show IO Nat from do
  let mut n := 0
  withInjected2 #[1, 2] "abc" (fun as s => do← n := as.size + s.length)
  return n

-- A pattern binder is rejected.
/-- error: A `do←` binder must be a variable. Bind a variable and `match` on it in the body. -/
#guard_msgs in
example : IO Nat := do
  let mut n := 0
  withInjected (1, 2) (fun (a, b) => do← n := a + b)
  return n

/-! ### Control-info assertion -/

-- The forwarded body has two regular exits (both `if` branches fall through).
-- The doExpr handler clamps `numRegularExits := 1`, so the outer `do` block
-- treats the application as a single-exit element and inlines the continuation
-- `s := "after-" ++ s; return s` directly, without introducing a join point.
/--
info: have this :=
  let s := "";
  do
  let p ←
    withFinalizer (pure ())
        (if true = true then
          let s := "then";
          pure () s
        else
          let s := "else";
          pure () s)
  let s : String := p.snd
  let s : String := "after-" ++ s
  pure s;
this : IO String
-/
#guard_msgs in
#check show IO String from do
  let mut s := ""
  withFinalizer (pure ()) (do←
    if true then s := "then" else s := "else")
  s := "after-" ++ s
  return s

end DoForwardTest
