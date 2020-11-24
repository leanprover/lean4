# Tactics

Tactics are metaprograms, that is, programs that create programs.
Lean is implemented in Lean, you can import its implementation using `import Lean`.
The `Lean` package is part of the Lean distribution.
You can use the functions in the `Lean` package to write your own metaprograms
that automate repetitive tasks when writing programs and proofs.

We provide the **tactic** domain specific language (DSL) for using the tactic framework.
The tactic DSL provides commands for creating terms (and proofs). You
don't need to import the `Lean` package for using the tactic DSL.
Simple extensions can be implemented using macros. More complex extensions require
the `Lean` package. Notation used to write Lean terms can be easily lifted to the tactic DSL.

Tactics are instructions that tell Lean how to construct a term or proof.
Tactics operate on holes also known as goals. Each hole represents a missing
part of the term you are trying to build. Internally these holes are represented
as metavariables. They have a type and a local context. The local context contains
all local variables in scope.

In the following example, we prove the same simple theorem using different tactics.
The keyword `by` instructs Lean to use the tactic DSL to construct a term.
Our initial goal is a hole with type `p ∨ q → q ∨ p`. We tactic `intro h`
fills this hole using the term `fun h => ?m` where `?m` is a new hole we need to solve.
This hole has type `q ∨ p`, and the local context contains `h : p ∨ q`.
The tactic `cases` fills the hole using `Or.casesOn h (fun h1 => ?m1) (fun h2 => ?m2)`
where `?m1` and `?m2` are new holes. The tactic `apply Or.inr` fills the hole `?m1`
with the application `Or.inr ?m3`, and `exact h1` fills `?m3` with `h1`.
The tactic `assumption` tries to fill a hole by searching the local context for a term with the same type.

```lean
theorem ex1 : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl h1 =>
    apply Or.inr
    exact h1
  | inr h2 =>
    apply Or.inl
    assumption

#print ex1
/-
theorem ex1 : {p q : Prop} → p ∨ q → q ∨ p :=
fun {p q : Prop} (h : p ∨ q) =>
  Or.casesOn h (fun (h1 : p) => Or.inr h1) fun (h2 : q) => Or.inl h2
-/

-- You can use `match-with` in tactics.
theorem ex2 : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2

-- As we have the `fun+match` syntax sugar for terms,
-- we have the `intro+match` syntax sugar
theorem ex3 : p ∨ q → q ∨ p := by
  intro
  | Or.inl h1 =>
    apply Or.inr
    exact h1
  | Or.inr h2 =>
    apply Or.inl
    assumption
```

The examples above are all structured, but Lean 4 still supports unstructured
proofs. Unstructured proofs are useful when creating reusable scripts that may
discharge different goals.
Here is an unstructured version of the example above.

```lean
theorem ex1 : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
  done -- fails with an error here if there are unsolvable goals

theorem ex2 : p ∨ q → q ∨ p := by
  intro h
  cases h
  focus -- instructs Lean to `focus` on the first goal,
    apply Or.inr
    assumption
    -- it will fail if there are still unsolvable goals here
  focus
    apply Or.inl
    assumption

theorem ex3 : p ∨ q → q ∨ p := by
  intro h
  cases h
  -- You can still use curly braces and semicolons instead of
  -- whitespace sensitive notation as in the previous example
  { apply Or.inr;
    assumption
    -- It will fail if there are unsolved goals
  }
  { apply Or.inl;
    assumption
  }

-- Many tactics tag subgoals. The tactic `cases` tag goals using constructor names.
-- The tactic `case tag => tactics` instructs Lean to solve the goal
-- with the matching tag.
theorem ex4 : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr =>
    apply Or.inl
    assumption
  case inl =>
    apply Or.inr
    assumption

-- Same example for curly braces and semicolons aficionados
theorem ex5 : p ∨ q → q ∨ p := by {
  intro h;
  cases h;
  case inr => {
    apply Or.inl;
    assumption
  }
  case inl => {
    apply Or.inr;
    assumption
  }
}
```

## Rewrite

TODO

## Pattern matching

As a convenience, pattern-matching has been integrated into tactics such as `intro` and `funext`.

```lean
theorem ex1 : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

theorem ex2 :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.addComm]
  rfl
```

## Induction

The `induction` tactic now supports user-defined induction principles with
multiple targets (aka major premises).


```lean
/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/

theorem ex (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn generalizing h with
  | ind x y h₁ ih =>
    rw [Nat.modEqSubMod h₁.2]
    exact ih h
  | base x y h₁ =>
     have ¬ 0 < y ∨ ¬ y ≤ x from Iff.mp (Decidable.notAndIffOrNot ..) h₁
     match this with
     | Or.inl h₁ => exact absurd h h₁
     | Or.inr h₁ =>
       have hgt : y > x from Nat.gtOfNotLe h₁
       rw [← Nat.modEqOfLt hgt] at hgt
       assumption
```

## Cases

TODO

## Injection

TODO

## Extensible tactics

In the following example, we define the notation `trivial` for the tactic DSL using
the command `syntax`. Then, we use the command `macro_rules` to specify what should
be done when `trivial` is used. You can provide different expansions, and the tactic DSL
interpreter will try all of them until one succeeds.

```lean
-- Define a new notation for the tactic DSL
syntax "trivial" : tactic

macro_rules
  | `(tactic| trivial) => `(tactic| assumption)

theorem ex1 (h : p) : p := by
  trivial

-- You cannot prove the following theorem using `trivial`
-- theorem ex2 (x : α) : x = x := by
--  trivial

-- Let's extend `trivial`. The `by` DSL interpreter
-- tries all possible macro extensions for `trivial` until one succeeds
macro_rules
  | `(tactic| trivial) => `(tactic| rfl)

theorem ex2 (x : α) : x = x := by
  trivial

theorem ex3 (x : α) (h : p) : x = x ∧ p := by
  apply And.intro
  repeat trivial
```

# `let-rec`

You can use `let rec` to write local recursive functions. We lifted it to the tactic DSL,
and you can use it to create proofs by induction.

```lean
def lengthReplicateEq {α} (n : Nat) (a : α) : (List.replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
      : (List.replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => rw [Nat.zeroAdd]; rfl
    | n+1 =>
      show List.length (List.replicate.loop a n (a::as)) = Nat.succ n + as.length
      rw [aux n, List.lengthConsEq, Nat.addSucc, Nat.succAdd]
      rfl
  exact aux n []
```

# `begin-end` lovers

If you love Lean 3 `begin ... end` tactic blocks and commas, you can define this notation
in Lean 4 using macros in a few lines of code.

```lean
open Lean in
macro "begin " ts:sepByT(tactic, ", ") "end" : term => do
  let stx  ← getRef
  let ts   := ts.getSepArgs.map (mkNullNode #[·, mkNullNode])
  let tseq := mkNode `Lean.Parser.Tactic.tacticSeqBracketed #[
     mkAtomFrom stx "{", mkNullNode ts, mkAtomFrom stx[2] "}"
  ]
  `(by $tseq:tacticSeqBracketed)

theorem ex (x : Nat) : x + 0 = 0 + x :=
  begin
    rw Nat.zeroAdd,
    rw Nat.addZero,
    rfl
  end
```
