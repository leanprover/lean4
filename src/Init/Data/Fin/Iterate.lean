/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
prelude
import Init.PropLemmas
import Init.Data.Fin.Basic

namespace Fin

/--
Applies an index-dependent function `f` to all of the values in `[i:n]`, starting at `i` with an
initial accumulator `a`.

Concretely, `Fin.hIterateFrom P f i a` is equal to
```lean
  a |> f i |> f (i + 1) |> ... |> f (n - 1)
```

Theorems about `Fin.hIterateFrom` can be proven using the general theorem `Fin.hIterateFrom_elim` or
other more specialized theorems.

`Fin.hIterate` is a variant that always starts at `0`.
-/
def hIterateFrom (P : Nat → Sort _) {n} (f : ∀(i : Fin n), P i.val → P (i.val+1))
      (i : Nat) (ubnd : i ≤ n) (a : P i) : P n :=
  if g : i < n then
    hIterateFrom P f (i+1) g (f ⟨i, g⟩ a)
  else
    have p : i = n := (or_iff_left g).mp (Nat.eq_or_lt_of_le ubnd)
    _root_.cast (congrArg P p) a
  termination_by n - i
  decreasing_by decreasing_trivial_pre_omega

/--
Applies an index-dependent function to all the values less than the given bound `n`, starting at
`0` with an accumulator.

Concretely, `Fin.hIterate P init f` is equal to
```lean
  init |> f 0 |> f 1 |> ... |> f (n-1)
```

Theorems about `Fin.hIterate` can be proven using the general theorem `Fin.hIterate_elim` or other more
specialized theorems.

`Fin.hIterateFrom` is a variant that takes a custom starting value instead of `0`.
 -/
def hIterate (P : Nat → Sort _) {n : Nat} (init : P 0) (f : ∀(i : Fin n), P i.val → P (i.val+1)) :
    P n :=
  hIterateFrom P f 0 (Nat.zero_le n) init

private theorem hIterateFrom_elim {P : Nat → Sort _}(Q : ∀(i : Nat), P i → Prop)
    {n  : Nat}
    (f : ∀(i : Fin n), P i.val → P (i.val+1))
    {i : Nat} (ubnd : i ≤ n)
    (s : P i)
    (init : Q i s)
    (step : ∀(k : Fin n) (s : P k.val), Q k.val s → Q (k.val+1) (f k s)) :
    Q n (hIterateFrom P f i ubnd s) := by
  let ⟨j, p⟩ := Nat.le.dest ubnd
  induction j generalizing i ubnd init with
  | zero =>
    unfold hIterateFrom
    have g : ¬ (i < n) := by simp at p; simp [p]
    have r : Q n (_root_.cast (congrArg P p) s) :=
      @Eq.rec Nat i (fun k eq => Q k (_root_.cast (congrArg P eq) s)) init n p
    simp only [g, r, dite_false]
  | succ j inv =>
    unfold hIterateFrom
    have d : Nat.succ i + j = n := by simp [Nat.succ_add]; exact p
    have g : i < n := Nat.le.intro d
    simp only [g]
    exact inv _ _ (step ⟨i,g⟩ s init) d

/-
`hIterate_elim` provides a mechanism for showing that the result of
`hIterate` satisfies a property `Q stop` by showing that the states
at the intermediate indices `i : start ≤ i < stop` satisfy `Q i`.
-/
theorem hIterate_elim {P : Nat → Sort _} (Q : ∀(i : Nat), P i → Prop)
    {n : Nat} (f : ∀(i : Fin n), P i.val → P (i.val+1)) (s : P 0) (init : Q 0 s)
    (step : ∀(k : Fin n) (s : P k.val), Q k.val s → Q (k.val+1) (f k s)) :
    Q n (hIterate P s f) := by
  exact hIterateFrom_elim _ _ _ _ init step

/-
`hIterate_eq`provides a mechanism for replacing `hIterate P s f` with a
function `state` showing that matches the steps performed by `hIterate`.

This allows rewriting incremental code using `hIterate` with a
non-incremental state function.
-/
theorem hIterate_eq {P : Nat → Sort _} (state : ∀(i : Nat), P i)
    {n : Nat} (f : ∀(i : Fin n), P i.val → P (i.val+1)) (s : P 0)
    (init : s = state 0)
    (step : ∀(i : Fin n), f i (state i) = state (i+1)) :
    hIterate P s f = state n := by
  apply hIterate_elim (fun i s => s = state i) f s init
  intro i s s_eq
  simp only [s_eq, step]
