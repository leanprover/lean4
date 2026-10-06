import Lean
/-!
Tests that `Sym.simp` unfolds definitions when a function symbol is provided as a parameter,
like `Meta.simp` does with `simp [f]`: using the equational theorems and, for non-recursive
definitions, the unfolding theorem `f.eq_def` as a fallback.
-/

def f (a : Nat) := a + a

-- Non-recursive definition: `simp [f]` uses `f.eq_1`
example : f 2 = 4 := by
  sym =>
    simp [f]

-- Recursive definition defined by pattern matching
def g : Nat → Nat
  | 0 => 1
  | n+1 => g n + 1

example : g 2 = 3 := by
  sym =>
    simp [g]

-- Prop-valued definition: unfolds to its value
def myDef : Prop := True

example : myDef := by
  sym =>
    simp [myDef]

-- Definitions also work in the `rewrite [...]` simproc DSL
register_sym_simp unfoldF where
  post := ground >> rewrite [f]

example : f 2 = 4 := by
  sym =>
    simp unfoldF

-- Non-recursive definition by pattern matching: the equational theorems `m.eq_1`/`m.eq_2`
-- are tried first, and `m.eq_def` unfolds the applications they do not cover.
def m (b : Bool) (x : Nat) : Nat :=
  match b with
  | true => x
  | false => 0

example (x : Nat) : m true x = x := by
  sym =>
    simp [m]

example (b : Bool) (x : Nat) : m b x = match b with | true => x | false => 0 := by
  sym =>
    simp [m]

-- Overlapping patterns produce the conditional equational theorem
-- `h.eq_2 : (x = 0 → False) → h x = x + 1`. It is tried before `h.eq_def`, so the goal is
-- closed without exposing a `match`.
def h : Nat → Nat
  | 0 => 0
  | n => n + 1

example : h 5 = 6 := by
  sym =>
    simp [h]

-- `h.eq_def` unfolds `h n` when neither equational theorem applies.
example (n : Nat) : h n = match n with | 0 => 0 | n => n + 1 := by
  sym =>
    simp [h]

-- Recursive definitions are unfolded by their equational theorems only.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (n : Nat) : g n = match n with | 0 => 1 | n + 1 => g n + 1 := by
  sym =>
    simp [g]

example (n : Nat) : g n = match n with | 0 => 1 | n + 1 => g n + 1 := by
  sym =>
    simp [g.eq_def]

-- The fallback also applies to definitions provided in the `rewrite [...]` simproc DSL.
register_sym_simp unfoldM where
  post := ground >> rewrite [m]

example (b : Bool) (x : Nat) : m b x = match b with | true => x | false => 0 := by
  sym =>
    simp unfoldM
