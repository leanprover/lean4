/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Basic
import Init.Control.Id
import Init.Control.Lawful
import Init.Data.List.Basic

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List
universe u v w u₁ u₂

/-!
Remark: we can define `mapM`, `mapM₂` and `forM` using `Applicative` instead of `Monad`.
Example:
```
def mapM {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
  | []    => pure []
  | a::as => List.cons <$> (f a) <*> mapM as
```

However, we consider `f <$> a <*> b` an anti-idiom because the generated code
may produce unnecessary closure allocations.
Suppose `m` is a `Monad`, and it uses the default implementation for `Applicative.seq`.
Then, the compiler expands `f <$> a <*> b <*> c` into something equivalent to
```
(Functor.map f a >>= fun g_1 => Functor.map g_1 b) >>= fun g_2 => Functor.map g_2 c
```
In an ideal world, the compiler may eliminate the temporary closures `g_1` and `g_2` after it inlines
`Functor.map` and `Monad.bind`. However, this can easily fail. For example, suppose
`Functor.map f a >>= fun g_1 => Functor.map g_1 b` expanded into a match-expression.
This is not unreasonable and can happen in many different ways, e.g., we are using a monad that
may throw exceptions. Then, the compiler has to decide whether it will create a join-point for
the continuation of the match or float it. If the compiler decides to float, then it will
be able to eliminate the closures, but it may not be feasible since floating match expressions
may produce exponential blowup in the code size.

Finally, we rarely use `mapM` with something that is not a `Monad`.

Users that want to use `mapM` with `Applicative` should use `mapA` instead.
-/

/--
Applies the monadic action `f` on every element in the list, left-to-right, and returns the list of
results.

This implementation is tail recursive. `List.mapM'` is a a non-tail-recursive variant that may be
more convenient to reason about. `List.forM` is the variant that discards the results and
`List.mapA` is the variant that works with `Applicative`.
-/
@[inline]
def mapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) (as : List α) : m (List β) :=
  let rec @[specialize] loop
    | [],      bs => pure bs.reverse
    | a :: as, bs => do loop as ((← f a)::bs)
  loop as []

/--
Applies the applicative action `f` on every element in the list, left-to-right, and returns the list
of results.

If `m` is also a `Monad`, then using `mapM` can be more efficient.

See `List.forA` for the variant that discards the results. See `List.mapM` for the variant that
works with `Monad`.

This function is not tail-recursive, so it may fail with a stack overflow on long lists.
-/
@[specialize]
def mapA {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
  | []    => pure []
  | a::as => List.cons <$> f a <*> mapA f as

/--
Applies the monadic action `f` to every element in the list, in order.

`List.mapM` is a variant that collects results. `List.forA` is a variant that works on any
`Applicative`.
-/
@[specialize]
protected def forM {m : Type u → Type v} [Monad m] {α : Type w} (as : List α) (f : α → m PUnit) : m PUnit :=
  match as with
  | []      => pure ⟨⟩
  | a :: as => do f a; List.forM as f

/--
Applies the applicative action `f` to every element in the list, in order.

If `m` is also a `Monad`, then using `List.forM` can be more efficient.

`List.mapA` is a variant that collects results.
-/
@[specialize]
def forA {m : Type u → Type v} [Applicative m] {α : Type w} (as : List α) (f : α → m PUnit) : m PUnit :=
  match as with
  | []      => pure ⟨⟩
  | a :: as => f a *> forA as f


@[specialize]
def filterAuxM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → List α → m (List α)
  | [],     acc => pure acc
  | h :: t, acc => do
    let b ← f h
    filterAuxM f t (cond b (h :: acc) acc)

/--
Applies the monadic predicate `p` to every element in the list, in order from left to right, and
returns the list of elements for which `p` returns `true`.

`O(|l|)`.

Example:
```lean example
#eval [1, 2, 5, 2, 7, 7].filterM fun x => do
  IO.println s!"Checking {x}"
  return x < 3
```
```output
Checking 1
Checking 2
Checking 5
Checking 2
Checking 7
Checking 7
```
```output
[1, 2, 2]
```
-/
@[inline]
def filterM {m : Type → Type v} [Monad m] {α : Type} (p : α → m Bool) (as : List α) : m (List α) := do
  let as ← filterAuxM p as []
  pure as.reverse

/--
Applies the monadic predicate `p` on every element in the list in reverse order, from right to left,
and returns those elements for which `p` returns `true`. The elements of the returned list are in
the same order as in the input list.

Example:
```lean example
#eval [1, 2, 5, 2, 7, 7].filterRevM fun x => do
  IO.println s!"Checking {x}"
  return x < 3
```
```output
Checking 7
Checking 7
Checking 2
Checking 5
Checking 2
Checking 1
```
```output
[1, 2, 2]
```
-/
@[inline]
def filterRevM {m : Type → Type v} [Monad m] {α : Type} (p : α → m Bool) (as : List α) : m (List α) :=
  filterAuxM p as.reverse []

/--
Applies a monadic function that returns an `Option` to each element of a list, collecting the
non-`none` values.

`O(|l|)`.

Example:
```lean example
#eval [1, 2, 5, 2, 7, 7].filterMapM fun x => do
  IO.println s!"Examining {x}"
  if x > 2 then return some (2 * x)
  else return none
```
```output
Examining 1
Examining 2
Examining 5
Examining 2
Examining 7
Examining 7
```
```output
[10, 14, 14]
```
-/
@[inline]
def filterMapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m (Option β)) (as : List α) : m (List β) :=
  let rec @[specialize] loop
    | [],     bs => pure bs.reverse
    | a :: as, bs => do
      match (← f a) with
      | none   => loop as bs
      | some b => loop as (b::bs)
  loop as []

/--
Applies a monadic function that returns a list to each element of a list, from left to right, and
concatenates the resulting lists.
-/
@[inline]
def flatMapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m (List β)) (as : List α) : m (List β) :=
  let rec @[specialize] loop
    | [],     bs => pure bs.reverse.flatten
    | a :: as, bs => do
      let bs' ← f a
      loop as (bs' :: bs)
  loop as []


/--
Folds a monadic function over a list from the left, accumulating a value starting with `init`. The
accumulated value is combined with the each element of the list in order, using `f`.

Example:
```lean example
example [Monad m] (f : α → β → m α) :
    List.foldlM (m := m) f x₀ [a, b, c] = (do
      let x₁ ← f x₀ a
      let x₂ ← f x₁ b
      let x₃ ← f x₂ c
      pure x₃)
  := by rfl
```
-/
@[specialize]
def foldlM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (f : s → α → m s) → (init : s) → List α → m s
  | _, s, []      => pure s
  | f, s, a :: as => do
    let s' ← f s a
    List.foldlM f s' as

@[simp] theorem foldlM_nil [Monad m] (f : β → α → m β) (b) : [].foldlM f b = pure b := rfl
@[simp] theorem foldlM_cons [Monad m] (f : β → α → m β) (b) (a) (l : List α) :
    (a :: l).foldlM f b = f b a >>= l.foldlM f := by
  simp [List.foldlM]

/--
Folds a monadic function over a list from the right, accumulating a value starting with `init`. The
accumulated value is combined with the each element of the list in order, using `f`.

Example:
```lean example
example [Monad m] (f : α → β → m β) :
  List.foldrM (m := m) f x₀ [a, b, c] = (do
    let x₁ ← f c x₀
    let x₂ ← f b x₁
    let x₃ ← f a x₂
    pure x₃)
  := by rfl
```
-/
@[inline]
def foldrM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} (f : α → s → m s) (init : s) (l : List α) : m s :=
  l.reverse.foldlM (fun s a => f a s) init

@[simp] theorem foldrM_nil [Monad m] (f : α → β → m β) (b) : [].foldrM f b = pure b := rfl

/--
Maps `f` over the list and collects the results with `<|>`. The result for the end of the list is
`failure`.

Examples:
 * `[[], [1, 2], [], [2]].firstM List.head? = some 1`
 * `[[], [], []].firstM List.head? = none`
 * `[].firstM List.head? = none`
-/
@[specialize]
def firstM {m : Type u → Type v} [Alternative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m β
  | []    => failure
  | a::as => f a <|> firstM f as

/--
Returns true if the monadic predicate `p` returns `true` for any element of `l`.

`O(|l|)`. Short-circuits upon encountering the first `true`. The elements in `l` are examined in
order from left to right.
-/
@[specialize]
def anyM {m : Type → Type u} [Monad m] {α : Type v} (p : α → m Bool) : (l : List α) → m Bool
  | []    => pure false
  | a::as => do
    match (← p a) with
    | true  => pure true
    | false => anyM p as

/--
Returns true if the monadic predicate `p` returns `true` for every element of `l`.

`O(|l|)`. Short-circuits upon encountering the first `false`. The elements in `l` are examined in
order from left to right.
-/
@[specialize]
def allM {m : Type → Type u} [Monad m] {α : Type v} (p : α → m Bool) : (l : List α) → m Bool
  | []    => pure true
  | a::as => do
    match (← p a) with
    | true  => allM p as
    | false => pure false

/--
Returns the first element of the list for which the monadic predicate `p` returns `true`, or `none`
if no such element is found. Elements of the list are checked in order.

`O(|l|)`.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
@[specialize]
def findM? {m : Type → Type u} [Monad m] {α : Type} (p : α → m Bool) : List α → m (Option α)
  | []    => pure none
  | a::as => do
    match (← p a) with
    | true  => pure (some a)
    | false => findM? p as

@[simp]
theorem findM?_pure {m} [Monad m] [LawfulMonad m] (p : α → Bool) (as : List α) :
    findM? (m := m) (pure <| p ·) as = pure (as.find? p) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [findM?, find?]
    cases p a with
    | true  => simp
    | false => simp [ih]

@[simp]
theorem findM?_id (p : α → Id Bool) (as : List α) :
    (findM? p as).run = as.find? (p · |>.run) :=
  findM?_pure _ _

/--
Returns the first non-`none` result of applying the monadic function `f` to each element of the
list, in order. Returns `none` if `f` returns `none` for all elements.

`O(|l|)`.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
@[specialize]
def findSomeM? {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m (Option β)) : List α → m (Option β)
  | []    => pure none
  | a::as => do
    match (← f a) with
    | some b => pure (some b)
    | none   => findSomeM? f as

@[simp]
theorem findSomeM?_pure [Monad m] [LawfulMonad m] (f : α → Option β) (as : List α) :
    findSomeM? (m := m) (pure <| f ·) as = pure (as.findSome? f) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [findSomeM?, findSome?]
    cases f a with
    | some b => simp
    | none   => simp [ih]

theorem findSomeM?_id (f : α → Id (Option β)) (as : List α) :
    (findSomeM? f as).run = as.findSome? (f · |>.run) :=
  findSomeM?_pure _ _

theorem findM?_eq_findSomeM? [Monad m] [LawfulMonad m] (p : α → m Bool) (as : List α) :
    as.findM? p = as.findSomeM? fun a => return if (← p a) then some a else none := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [findM?, findSomeM?]
    simp [ih]
    congr
    apply funext
    intro b
    cases b <;> simp

@[inline] protected def forIn' {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : List α) (init : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop : (as' : List α) → (b : β) → Exists (fun bs => bs ++ as' = as) → m β
    | [], b, _    => pure b
    | a::as', b, h => do
      have : a ∈ as := by
        clear f
        have ⟨bs, h⟩ := h
        subst h
        exact mem_append_right _ (Mem.head ..)
      match (← f a this b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b =>
        have : Exists (fun bs => bs ++ as' = as) := have ⟨bs, h⟩ := h; ⟨bs ++ [a], by rw [← h, append_cons bs a as']⟩
        loop as' b this
  loop as init ⟨[], rfl⟩

instance : ForIn' m (List α) α inferInstance where
  forIn' := List.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

-- We simplify `List.forIn'` to `forIn'`.
@[simp] theorem forIn'_eq_forIn' [Monad m] : @List.forIn' α β m _ = forIn' := rfl

@[simp] theorem forIn'_nil [Monad m] (f : (a : α) → a ∈ [] → β → m (ForInStep β)) (b : β) : forIn' [] b f = pure b :=
  rfl

@[simp] theorem forIn_nil [Monad m] (f : α → β → m (ForInStep β)) (b : β) : forIn [] b f = pure b :=
  rfl

instance : ForM m (List α) α where
  forM := List.forM

-- We simplify `List.forM` to `forM`.
@[simp] theorem forM_eq_forM [Monad m] : @List.forM m _ α = forM := rfl

@[simp] theorem forM_nil  [Monad m] (f : α → m PUnit) : forM [] f = pure ⟨⟩ :=
  rfl
@[simp] theorem forM_cons [Monad m] (f : α → m PUnit) (a : α) (as : List α) : forM (a::as) f = f a >>= fun _ => forM as f :=
  rfl

instance : Functor List where
  map := List.map

end List
