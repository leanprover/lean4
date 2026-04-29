import Lean

/-!
Tests for the pluggable pure/bind builders in the `do` elaborator (`DoOps`, `elabDoWith`).

We define a surface `ido` notation that reuses the full `do` elaborator via `elabDoWith`
but emits `IxMonad.pure` / `IxMonad.bind` instead of `Pure.pure` / `Bind.bind`.

`IxMonad` is the canonical Atkey parameterised monad (`m : ι → ι → Type u → Type v` with
`pure : α → m i i α` and `bind : m i j α → (α → m j k β) → m i k β`); the shape is
documented in `Control.Monad.Indexed` on Hackage and the PureScript `indexed-monad`
package.

The control-stack features of `do` (`mut`, `return`, `break`, `continue`, `for`) remain
hard-coded to `Monad` and are therefore off-limits for `ido`. The `ido` programs below
avoid them.
-/

open Lean Lean.Parser Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term

set_option backward.do.legacy false

/-! ## Indexed monad and a concrete instance -/

class IxMonad (m : ι → ι → Type u → Type v) where
  pure : α → m i i α
  bind : m i j α → (α → m j k β) → m i k β

/-- Atkey-style indexed state: `IState i o α = i → α × o`. -/
abbrev IState (i o α : Type) : Type := i → α × o

instance : IxMonad IState where
  pure a := fun i => (a, i)
  bind p f := fun i => let (a, j) := p i; f a j

/-! Helpers that keep the state type fixed at `Nat` for the common examples. -/

def getN : IState Nat Nat Nat := fun s => (s, s)
def putN (n : Nat) : IState Nat Nat Unit := fun _ => ((), n)
def modifyN (f : Nat → Nat) : IState Nat Nat Unit := fun i => ((), f i)

/-! ## Pluggable ops emitting `IxMonad.pure` / `IxMonad.bind` -/

def ixOps : DoOps where
  mkPureApp α e := do
    let info := (← read).monadInfo
    let mα := mkApp info.m α
    let eStx ← Term.exprToSyntax e
    let stx ← `(IxMonad.pure $eStx)
    Term.elabTermEnsuringType stx mα
  mkBindApp α β e k := do
    let info := (← read).monadInfo
    let mβ := mkApp info.m β
    let eStx ← Term.exprToSyntax e
    let kStx ← Term.exprToSyntax k
    let stx ← `(IxMonad.bind $eStx $kStx)
    Term.elabTermEnsuringType stx mβ
  isPureApp? e :=
    -- `@IxMonad.pure ι m inst α i e` — 6 args.
    if e.isAppOfArity ``IxMonad.pure 6 then some (e.getArg! 5) else none

/-! ## `ido` surface syntax -/

syntax (name := idoKind) "ido " doSeq : term

@[term_elab idoKind] def elabIDo : Term.TermElab := fun stx et? => do
  let `(ido $doSeq) := stx | throwUnsupportedSyntax
  elabDoWith ixOps doSeq et?

/-! ## Example programs

Each example pairs `#guard_msgs` with `#eval` (or `#check`) to lock behaviour in.
Most keep state type fixed at `Nat`; a couple at the end explore index-preserving
variants with different state types. -/

/-! ### 1. Bare pure -/

/-- info: (42, 10) -/
#guard_msgs in
#eval (ido IxMonad.pure 42 : IState Nat Nat Nat) 10

/-! ### 2. Monadic `let ← ` -/

/-- info: (11, 10) -/
#guard_msgs in
#eval (ido do
  let x ← getN
  IxMonad.pure (x + 1) : IState Nat Nat Nat) 10

/-! ### 3. Plain `let :=` -/

/-- info: (20, 10) -/
#guard_msgs in
#eval (ido do
  let x := 10
  let y ← getN
  IxMonad.pure (x + y) : IState Nat Nat Nat) 10

/-! ### 4. Sequential unit-typed element -/

/-- info: (11, 11) -/
#guard_msgs in
#eval (ido do
  modifyN (· + 1)
  getN : IState Nat Nat Nat) 10

/-! ### 5. Multi-step chain -/

/-- info: ((10, 11), 11) -/
#guard_msgs in
#eval (ido do
  let a ← getN
  modifyN (· + 1)
  let b ← getN
  IxMonad.pure (a, b) : IState Nat Nat (Nat × Nat)) 10

/-! ### 6. Nested `(← …)` in pure context -/

/-- info: (11, 10) -/
#guard_msgs in
#eval (ido IxMonad.pure ((← getN) + 1) : IState Nat Nat Nat) 10

/-! ### 7. Nested `(← …)` appearing twice in one expression -/

/-- info: (20, 10) -/
#guard_msgs in
#eval (ido IxMonad.pure ((← getN) + (← getN)) : IState Nat Nat Nat) 10

/-! ### 8. `if/then/else` with do branches -/

/-- info: (5, 5) -/
#guard_msgs in
#eval (ido do
  let x ← getN
  if x > 0 then IxMonad.pure x else IxMonad.pure 0 : IState Nat Nat Nat) 5

/-- info: (0, 0) -/
#guard_msgs in
#eval (ido do
  let x ← getN
  if x > 0 then IxMonad.pure x else IxMonad.pure 0 : IState Nat Nat Nat) 0

/-! ### 9. `if` with a lifted action in the condition -/

/-- info: ((), 4) -/
#guard_msgs in
#eval (ido do
  if (← getN) > 0 then modifyN (· - 1) else IxMonad.pure () : IState Nat Nat Unit) 5

/-- info: ((), 0) -/
#guard_msgs in
#eval (ido do
  if (← getN) > 0 then modifyN (· - 1) else IxMonad.pure () : IState Nat Nat Unit) 0

/-! ### 10. `match` dispatching into do blocks -/

/-- info: (100, 7) -/
#guard_msgs in
#eval (ido do
  match (← getN) with
  | 0 => IxMonad.pure 0
  | _ => IxMonad.pure 100 : IState Nat Nat Nat) 7

/-! ### 11. Pattern `let` -/

/-- info: (3, 0) -/
#guard_msgs in
#eval (ido do
  let (a, b) ← IxMonad.pure (1, 2)
  IxMonad.pure (a + b) : IState Nat Nat Nat) 0

/-! ### 12. Nested `ido` inside `ido` -/

/-- info: (42, 0) -/
#guard_msgs in
#eval (ido do
  let y ← (ido IxMonad.pure 42 : IState Nat Nat Nat)
  IxMonad.pure y : IState Nat Nat Nat) 0

/-! ### 13. `ido` composing with ordinary `do` -/

/-- info: 84 -/
#guard_msgs in
#eval Id.run do
  let (n, _) := (ido IxMonad.pure 42 : IState Nat Nat Nat) 0
  pure (n * 2)

/-! ### 14. `pure e >>= pure` peephole — confirms the generated term has no redundant
         `IxMonad.bind`.

The equation `(ido do let x ← IxMonad.pure 17; IxMonad.pure x) = IxMonad.pure 17` holds
definitionally only if the peephole in `mkBindUnlessPure` fired and contracted the bind
away, emitting a bare `IxMonad.pure 17`. If the peephole failed, the result would be
`IxMonad.bind (IxMonad.pure 17) IxMonad.pure`, which is not definitionally equal to
`IxMonad.pure 17` because `IxMonad` is a plain `class` without beta-reduction laws. -/

example : (ido do
    let x ← IxMonad.pure 17
    IxMonad.pure x : IState Nat Nat Nat) = IxMonad.pure 17 := rfl

/-! ### 15. Deeper chains of binds -/

/-- info: (6, 10) -/
#guard_msgs in
#eval (ido do
  let a ← IxMonad.pure 1
  let b ← IxMonad.pure 2
  let c ← IxMonad.pure 3
  IxMonad.pure (a + b + c) : IState Nat Nat Nat) 10

/-! ### 16. Index-preserving monad with a different fixed state type -/

/-- info: ("hi there", "hi") -/
#guard_msgs in
#eval (ido do
  let s ← (fun (σ : String) => (σ, σ) : IState String String String)
  IxMonad.pure (s ++ " there") : IState String String String) "hi"
