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
Our initial goal is a hole with type `p ∨ q → q ∨ p`. The tactic `intro h`
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
  rw [Nat.add_comm]
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
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
     have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
     match this with
     | Or.inl h₁ => exact absurd h h₁
     | Or.inr h₁ =>
       have hgt : y > x := Nat.gt_of_not_le h₁
       rw [← Nat.mod_eq_of_lt hgt] at hgt
       assumption
```

## Cases

TODO

## Injection

TODO

## Dependent pattern matching

The `match-with` expression implements dependent pattern matching. You can use it to create concise proofs.

```lean
inductive Mem : α → List α → Prop where
  | head (a : α) (as : List α)   : Mem a (a::as)
  | tail (a b : α) (bs : List α) : Mem a bs → Mem a (b::bs)

infix:50 "∈" => Mem

theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t :=
  match a, as, h with
  | _, _, Mem.head a bs     => ⟨[], ⟨bs, rfl⟩⟩
  | _, _, Mem.tail a b bs h =>
    match bs, mem_split h with
    | _, ⟨s, ⟨t, rfl⟩⟩ => ⟨b::s, ⟨t, List.cons_append .. ▸ rfl⟩⟩
```

In the tactic DSL, the right-hand-side of each alternative in a `match-with` is a sequence of tactics instead of a term.
Here is a similar proof using the tactic DSL.

```lean
# inductive Mem : α → List α → Prop where
#  | head (a : α) (as : List α)   : Mem a (a::as)
#  | tail (a b : α) (bs : List α) : Mem a bs → Mem a (b::bs)
# infix:50 "∈" => Mem
theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t := by
  match a, as, h with
  | _, _, Mem.head a bs     => exists []; exists bs; rfl
  | _, _, Mem.tail a b bs h =>
    match bs, mem_split h with
    | _, ⟨s, ⟨t, rfl⟩⟩ =>
      exists b::s; exists t;
      rw [List.cons_append]
```

We can use `match-with` nested in tactics.
Here is a similar proof that uses the `induction` tactic instead of recursion.

```lean
# inductive Mem : α → List α → Prop where
#  | head (a : α) (as : List α)   : Mem a (a::as)
#  | tail (a b : α) (bs : List α) : Mem a bs → Mem a (b::bs)
# infix:50 "∈" => Mem
theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t := by
  induction as with
  | nil          => cases h
  | cons b bs ih => cases h with
    | head a bs => exact ⟨[], ⟨bs, rfl⟩⟩
    | tail a b bs h =>
      match bs, ih h with
      | _, ⟨s, ⟨t, rfl⟩⟩ =>
        exists b::s; exists t
        rw [List.cons_append]
```

You can create your own notation using existing tactics. In the following example,
we define a simple `obtain` tactic using macros. We say it is simple because it takes only one
discriminant. Later, we show how to create more complex automation using macros.

```lean
# inductive Mem : α → List α → Prop where
#  | head (a : α) (as : List α)   : Mem a (a::as)
#  | tail (a b : α) (bs : List α) : Mem a bs → Mem a (b::bs)
# infix:50 "∈" => Mem
macro "obtain " p:term " from " d:term : tactic =>
  `(tactic| match $d:term with | $p:term => ?_)

theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t := by
  induction as with
  | cons b bs ih => cases h with
    | tail a b bs h =>
      obtain ⟨s, ⟨t, h⟩⟩ from ih h
      exists b::s; exists t
      rw [h, List.cons_append]
    | head a bs => exact ⟨[], ⟨bs, rfl⟩⟩
  | nil => cases h

```

## Extensible tactics

In the following example, we define the notation `triv` for the tactic DSL using
the command `syntax`. Then, we use the command `macro_rules` to specify what should
be done when `triv` is used. You can provide different expansions, and the tactic DSL
interpreter will try all of them until one succeeds.

```lean
-- Define a new notation for the tactic DSL
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

theorem ex1 (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- theorem ex2 (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The `by` DSL interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

theorem ex2 (x : α) : x = x := by
  triv

theorem ex3 (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv
```

# `let-rec`

You can use `let rec` to write local recursive functions. We lifted it to the tactic DSL,
and you can use it to create proofs by induction.

```lean
theorem length_replicate {α} (n : Nat) (a : α) : (List.replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
      : (List.replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => rw [Nat.zero_add]; rfl
    | n+1 =>
      show List.length (List.replicate.loop a n (a::as)) = Nat.succ n + as.length
      rw [aux n, List.length_cons, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

You can also introduce auxiliary recursive declarations using `where` clause after your definition.
Lean converts them into a `let rec`.

```lean
theorem length_replicate {α} (n : Nat) (a : α) : (List.replicate n a).length = n :=
  loop n []
where
  loop n as : (List.replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => rw [Nat.zero_add]; rfl
    | n+1 =>
      show List.length (List.replicate.loop a n (a::as)) = Nat.succ n + as.length
      rw [loop n, List.length_cons, Nat.add_succ, Nat.succ_add]
```

# `begin-end` lovers

If you love Lean 3 `begin ... end` tactic blocks and commas, you can define this notation
in Lean 4 using macros in a few lines of code.

```lean
{{#include ../tests/lean/beginEndAsMacro.lean:doc}}
```
