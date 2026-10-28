/-!
Regression test for #15700.

`abstractGroundMismatches?` abstracts ground subterms that occur under binders and are equal in
the current goal, producing `abstractFn f a₁ ... aₙ`. It passed the abstracted terms in reverse
order, so with two or more of them the proof term was ill-typed and the kernel rejected it. Its
cache also ignored the number of enclosing binders, so a pair met again under more binders reused
a stale de Bruijn index.
-/
set_option grind.debug true

-- Two abstracted terms: `xs.length` and `getElem! xs`.
def headPos (xs : List Nat) (h : ∀ i, i < xs.length → 0 < xs[i]!) : Nat :=
  match xs with
  | a :: _ => a
  | [] => 1

example (xs : List Nat) (h : ∀ i, i < xs.length → 0 < xs[i]!) (hx : xs = [3]) :
    headPos xs h = 3 := by
  grind [headPos]

-- Three abstracted terms of different types.
def headPos3 (xs : List Nat) (n : Nat) (h : ∀ i, i < xs.length → n ≤ xs[i]! ∧ xs.head? ≠ none) :
    Nat :=
  match xs with
  | a :: _ => a
  | [] => 1

example (xs : List Nat) (n : Nat) (h : ∀ i, i < xs.length → n ≤ xs[i]! ∧ xs.head? ≠ none)
    (hx : xs = [3]) : headPos3 xs n h = 3 := by
  grind [headPos3]

-- The same pair `(x, some 1)` occurs under one binder and again under three binders.
def dep (x : Option Nat) (h : ∀ a, x = some a → ∀ b, x = some b → a = b) : Nat :=
  match x with
  | some a => a
  | none => 0

example (x : Option Nat) (hx : x = some 1) (H : ∀ a, x = some a → ∀ b, x = some b → a = b) :
    dep x H = 1 := by
  grind [dep]

-- One abstracted term: this already worked.
def headPos1 (xs : List Nat) (h : ∀ i, i < xs.length → 0 < i + 1) : Nat :=
  match xs with
  | a :: _ => a
  | [] => 1

example (xs : List Nat) (h : ∀ i, i < xs.length → 0 < i + 1) (hx : xs = [3]) :
    headPos1 xs h = 3 := by
  grind [headPos1]
