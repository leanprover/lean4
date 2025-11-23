/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Harun Khan, Fady Adal
-/
module

prelude
import all Init.Data.BitVec.Basic
public import Init.Data.BitVec.Lemmas
public import Init.Data.Fin.Iterate
public import Init.Data.Nat.Fold

public section

set_option linter.missingDocs true

namespace BitVec

/--
Constructs a bitvector by iteratively computing a state for each bit using the function `f`,
starting with the initial state `s`. At each step, the prior state and the current bit index are
passed to `f`, and it produces a bit along with the next state value. These bits are assembled into
the final bitvector.

It produces a sequence of state values `[s_0, s_1 .. s_w]` and a bitvector `v` where `f i s_i =
(s_{i+1}, b_i)` and `b_i` is bit `i`th least-significant bit in `v` (e.g., `getLsb v i = b_i`).

The theorem `iunfoldr_replace` allows uses of `BitVec.iunfoldr` to be replaced with declarative
specifications that are easier to reason about.
-/
def iunfoldr (f : Fin w → α → α × Bool) (s : α) : α × BitVec w :=
  Fin.hIterate (fun i => α × BitVec i) (s, nil) fun i q =>
    (fun p => ⟨p.fst, cons p.snd q.snd⟩) (f i q.fst)

theorem iunfoldr.fst_eq
    {f : Fin w → α → α × Bool} (state : Nat → α) (s : α)
    (init : s = state 0)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
    (iunfoldr f s).fst = state w := by
  unfold iunfoldr
  apply Fin.hIterate_elim (fun i (p : α × BitVec i) => p.fst = state i)
  case init =>
    exact init
  case step =>
    intro i ⟨s, v⟩ p
    simp_all [ind i]

private theorem iunfoldr.eq_test
    {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.val) = (state (i.val+1), value.getLsbD i.val)) :
    iunfoldr f a = (state w, BitVec.truncate w value) := by
  apply Fin.hIterate_eq (fun i => ((state i, BitVec.truncate i value) : α × BitVec i))
  case init =>
    simp only [init, eq_nil]
  case step =>
    intro i
    simp_all [setWidth_succ]

theorem iunfoldr_getLsbD' {f : Fin w → α → α × Bool} (state : Nat → α)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
  (∀ i : Fin w, getLsbD (iunfoldr f (state 0)).snd i.val = (f i (state i.val)).snd)
  ∧ (iunfoldr f (state 0)).fst = state w := by
  unfold iunfoldr
  simp
  apply Fin.hIterate_elim
        (fun j (p : α × BitVec j) => (hj : j ≤ w) →
         (∀ i : Fin j,  getLsbD p.snd i.val = (f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hj⟩ (state i.val)).snd)
          ∧ p.fst = state j)
  case hj => simp
  case init =>
    intro
    apply And.intro
    · intro i
      have := Fin.pos i
      contradiction
    · rfl
  case step =>
    intro j ⟨s, v⟩ ih hj
    apply And.intro
    case left =>
      intro i
      simp only [getLsbD_cons]
      have hj2 : j.val ≤ w := by simp
      cases (Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt)) with
      | inl h3 => simp [(Nat.ne_of_lt h3)]
                  exact (ih hj2).1 ⟨i.val, h3⟩
      | inr h3 => simp [h3]
                  cases (Nat.eq_zero_or_pos j.val) with
                  | inl hj3 => congr
                               rw [← (ih hj2).2]
                  | inr hj3 => congr
                               exact (ih hj2).2
    case right =>
      simp
      have hj2 : j.val ≤ w := by simp
      rw [← ind j, ← (ih hj2).2]


theorem iunfoldr_getLsbD {f : Fin w → α → α × Bool} (state : Nat → α) (i : Fin w)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
  getLsbD (iunfoldr f (state 0)).snd i.val = (f i (state i.val)).snd := by
  exact (iunfoldr_getLsbD' state ind).1 i

/--
Given a function `state` that provides the correct state for every potential iteration count and a
function that computes these states from the correct initial state, the result of applying
`BitVec.iunfoldr f` to the initial state is the state corresponding to the bitvector's width paired
with the bitvector that consists of each computed bit.

This theorem can be used to prove properties of functions that are defined using `BitVec.iunfoldr`.
-/
theorem iunfoldr_replace
    {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.val) = (state (i.val+1), value[i.val])) :
    iunfoldr f a = (state w, value) := by
  simp [iunfoldr.eq_test state value a init step]

theorem iunfoldr_replace_snd
  {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.val) = (state (i.val+1), value[i.val])) :
    (iunfoldr f a).snd = value := by
  simp [iunfoldr.eq_test state value a init step]

/-!
## Induction principle

Induction principle for treating `BitVec` as a container, building up from LSB to MSB.
-/

/--
Induction principle for bitvectors, viewing them as built from `cons`.

This allows reasoning about bitvectors by induction on their structure:
- Base case: `nil : BitVec 0`
- Inductive case: `cons b x : BitVec (w+1)` where `x : BitVec w`

Example usage:
```lean
theorem my_theorem (x : BitVec w) : P x := by
  induction x using BitVec.induction with
  | nil => -- prove P nil
  | cons b x ih => -- prove P (cons b x) using ih : P x
```
-/
@[elab_as_elim]
def induction {motive : ∀ {w}, BitVec w → Prop}
    (nil : motive nil)
    (cons : ∀ w (b : Bool) (x : BitVec w), motive x → motive (cons b x))
    {w : Nat} (x : BitVec w) : motive x := by
  induction w with
  | zero =>
    rw [eq_nil x]
    exact nil
  | succ w ih =>
    rw [←cons_msb_setWidth x]
    exact cons w x.msb (setWidth w x) (ih (setWidth w x))

/--
Fold a function over the bits of a bitvector from least significant to most significant.

`foldr (cons b x) f init = f b (foldr x f init)`
-/
def foldr (f : Bool → α → α) (init : α) (x : BitVec w) : α :=
  w.fold (fun i h acc => f x[i] acc) init

@[simp]
theorem foldr_nil : foldr f a nil = a := by
  simp [foldr]

@[simp]
theorem foldr_cons {x : BitVec w} : foldr f a (cons b x) = f b (foldr f a x) := by
  simp only [foldr, getElem_cons, Nat.fold_succ, ↓reduceDIte]
  congr
  ext
  rw [dif_neg (by omega)]

/--
Fold a function over the bits of a bitvector from least significant to most significant,
accumulating from the left.

`foldl (cons b x) f init = foldl x f (f init b)`
-/
def foldl (f : α → Bool → α) (init : α) (x : BitVec w) : α :=
  w.foldRev (fun i h acc => f acc x[i]) init

@[simp]
theorem foldl_nil : foldl f a nil = a := by
  simp [foldl]

@[simp]
theorem foldl_cons {x : BitVec w} : foldl f a (cons b x) = foldl f (f a b) x := by
  simp [foldl, getElem_cons, Nat.foldRev_succ, ↓reduceDIte]
  congr
  ext
  rw [dif_neg (by omega)]

/-!
## Indexed fold operations
-/

/--
Right fold with index.
Processes bits from LSB to MSB, providing the index to the function.
-/
def foldrIdx (f : Fin w → Bool → α → α) (init : α) (x : BitVec w) : α :=
  w.fold (fun i h acc => f ⟨i, h⟩ x[i] acc) init

@[simp]
theorem foldrIdx_nil : foldrIdx f a nil = a := by
  simp [foldrIdx]

@[simp]
theorem foldrIdx_cons {x : BitVec w} :
    foldrIdx f a (cons b x) = f ⟨w, by omega⟩ b (foldrIdx (fun i => f ⟨i.val, by omega⟩) a x) := by
  simp [foldrIdx, getElem_cons]
  congr
  ext
  rw [dif_neg (by omega)]

/--
Left fold with index.
Processes bits from MSB to LSB, providing the index to the function.
-/
def foldlIdx (f : α → Fin w → Bool → α) (init : α) (x : BitVec w) : α :=
  w.foldRev (fun i h acc => f acc ⟨i, h⟩ x[i]) init


@[simp]
theorem foldlIdx_nil : foldlIdx f a nil = a := by
  simp [foldlIdx]

@[simp]
theorem foldlIdx_cons {x : BitVec w} :
    foldlIdx f a (cons b x) = foldlIdx (fun acc i => f acc ⟨i.val, by omega⟩) (f a ⟨w, by omega⟩ b) x := by
  simp [foldlIdx, getElem_cons, Nat.foldRev_succ, ↓reduceDIte]
  congr
  ext
  rw [dif_neg (by omega)]

/-!
## Aggregation operations

These are specialized folds for common queries.
-/

/-- Check if all bits satisfy a predicate. -/
def all (x : BitVec w) (p : Bool → Bool) : Bool :=
  x.foldr (fun b acc => p b && acc) true

/-- Check if any bit satisfies a predicate. -/
def any (x : BitVec w) (p : Bool → Bool) : Bool :=
  x.foldr (fun b acc => p b || acc) false

@[simp]
theorem all_nil (p : Bool → Bool) : all nil p = true := by
  simp [all, -ofNat_eq_ofNat]

@[simp]
theorem any_nil (p : Bool → Bool) : any nil p = false := by
  simp [any, -ofNat_eq_ofNat]

@[simp]
theorem all_cons {x : BitVec w} : all (cons b x) p = (p b && all x p) := by
  simp [all]

@[simp]
theorem any_cons {x : BitVec w} : any (cons b x) p = (p b || any x p) := by
  simp [any]

/--
Monadic right fold over the bits of a bitvector from least significant to most significant.
-/
def foldrM {m : Type u → Type v} [Monad m] (x : BitVec w) (f : α → Bool → m α) (init : α) : m α :=
  w.fold (fun i h acc => do
    let a ← acc
    f a x[i]) (pure init)

/--
Monadic left fold over the bits of a bitvector from least significant to most significant.
-/
def foldlM {m : Type u → Type v} [Monad m] (x : BitVec w) (f : Bool → α → m α) (init : α) : m α :=
  w.foldRev (fun i h acc => do
    let a ← acc
    f x[i] a) (pure init)

end BitVec
