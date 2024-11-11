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

See `List.forM` for the variant that discards the results.
See `List.mapA` for the variant that works with `Applicative`.
-/
@[inline]
def mapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) (as : List α) : m (List β) :=
  let rec @[specialize] loop
    | [],      bs => pure bs.reverse
    | a :: as, bs => do loop as ((← f a)::bs)
  loop as []

/--
Applies the applicative action `f` on every element in the list, left-to-right, and returns the list of
results.

NB: If `m` is also a `Monad`, then using `mapM` can be more efficient.

See `List.forA` for the variant that discards the results.
See `List.mapM` for the variant that works with `Monad`.

**Warning**: this function is not tail-recursive, meaning that it may fail with a stack overflow on long lists.
-/
@[specialize]
def mapA {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
  | []    => pure []
  | a::as => List.cons <$> f a <*> mapA f as

/--
Applies the monadic action `f` on every element in the list, left-to-right.

See `List.mapM` for the variant that collects results.
See `List.forA` for the variant that works with `Applicative`.
-/
@[specialize]
protected def forM {m : Type u → Type v} [Monad m] {α : Type w} (as : List α) (f : α → m PUnit) : m PUnit :=
  match as with
  | []      => pure ⟨⟩
  | a :: as => do f a; List.forM as f

/--
Applies the applicative action `f` on every element in the list, left-to-right.

NB: If `m` is also a `Monad`, then using `forM` can be more efficient.

See `List.mapA` for the variant that collects results.
See `List.forM` for the variant that works with `Monad`.
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
Applies the monadic predicate `p` on every element in the list, left-to-right, and returns those
elements `x` for which `p x` returns `true`.
-/
@[inline]
def filterM {m : Type → Type v} [Monad m] {α : Type} (p : α → m Bool) (as : List α) : m (List α) := do
  let as ← filterAuxM p as []
  pure as.reverse

/--
Applies the monadic predicate `p` on every element in the list, right-to-left, and returns those
elements `x` for which `p x` returns `true`.
-/
@[inline]
def filterRevM {m : Type → Type v} [Monad m] {α : Type} (p : α → m Bool) (as : List α) : m (List α) :=
  filterAuxM p as.reverse []

/--
Applies the monadic function `f` on every element `x` in the list, left-to-right, and returns those
results `y` for which `f x` returns `some y`.
-/
@[inline]
def filterMapM {m : Type u → Type v} [Monad m] {α β : Type u} (f : α → m (Option β)) (as : List α) : m (List β) :=
  let rec @[specialize] loop
    | [],     bs => pure bs.reverse
    | a :: as, bs => do
      match (← f a) with
      | none   => loop as bs
      | some b => loop as (b::bs)
  loop as []

/--
Folds a monadic function over a list from left to right:
```
foldlM f x₀ [a, b, c] = do
  let x₁ ← f x₀ a
  let x₂ ← f x₁ b
  let x₃ ← f x₂ c
  pure x₃
```
-/
@[specialize]
protected def foldlM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (f : s → α → m s) → (init : s) → List α → m s
  | _, s, []      => pure s
  | f, s, a :: as => do
    let s' ← f s a
    List.foldlM f s' as

@[simp] theorem foldlM_nil [Monad m] (f : β → α → m β) (b) : [].foldlM f b = pure b := rfl
@[simp] theorem foldlM_cons [Monad m] (f : β → α → m β) (b) (a) (l : List α) :
    (a :: l).foldlM f b = f b a >>= l.foldlM f := by
  simp [List.foldlM]

/--
Folds a monadic function over a list from right to left:
```
foldrM f x₀ [a, b, c] = do
  let x₁ ← f c x₀
  let x₂ ← f b x₁
  let x₃ ← f a x₂
  pure x₃
```
-/
@[inline]
def foldrM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} (f : α → s → m s) (init : s) (l : List α) : m s :=
  l.reverse.foldlM (fun s a => f a s) init

@[simp] theorem foldrM_nil [Monad m] (f : α → β → m β) (b) : [].foldrM f b = pure b := rfl

/--
Maps `f` over the list and collects the results with `<|>`.
```
firstM f [a, b, c] = f a <|> f b <|> f c <|> failure
```
-/
@[specialize]
def firstM {m : Type u → Type v} [Alternative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m β
  | []    => failure
  | a::as => f a <|> firstM f as

@[specialize]
def anyM {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
  | []    => pure false
  | a::as => do
    match (← f a) with
    | true  => pure true
    | false => anyM f as

@[specialize]
def allM {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
  | []    => pure true
  | a::as => do
    match (← f a) with
    | true  => allM f as
    | false => pure false

@[specialize]
def findM? {m : Type → Type u} [Monad m] {α : Type} (p : α → m Bool) : List α → m (Option α)
  | []    => pure none
  | a::as => do
    match (← p a) with
    | true  => pure (some a)
    | false => findM? p as

@[simp]
theorem findM?_id (p : α → Bool) (as : List α) : findM? (m := Id) p as = as.find? p := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [findM?, find?]
    cases p a with
    | true  => rfl
    | false => rw [ih]; rfl

@[specialize]
def findSomeM? {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m (Option β)) : List α → m (Option β)
  | []    => pure none
  | a::as => do
    match (← f a) with
    | some b => pure (some b)
    | none   => findSomeM? f as

@[simp]
theorem findSomeM?_id (f : α → Option β) (as : List α) : findSomeM? (m := Id) f as = as.findSome? f := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [findSomeM?, findSome?]
    cases f a with
    | some b => rfl
    | none   => rw [ih]; rfl

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
        have ⟨bs, h⟩ := h
        subst h
        exact mem_append_of_mem_right _ (Mem.head ..)
      match (← f a this b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b =>
        have : Exists (fun bs => bs ++ as' = as) := have ⟨bs, h⟩ := h; ⟨bs ++ [a], by rw [← h, append_cons bs a as']⟩
        loop as' b this
  loop as init ⟨[], rfl⟩

instance : ForIn' m (List α) α inferInstance where
  forIn' := List.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

@[simp] theorem forIn'_eq_forIn' [Monad m] : @List.forIn' α β m _ = forIn' := rfl

@[simp] theorem forIn'_nil [Monad m] (f : (a : α) → a ∈ [] → β → m (ForInStep β)) (b : β) : forIn' [] b f = pure b :=
  rfl

@[simp] theorem forIn_nil [Monad m] (f : α → β → m (ForInStep β)) (b : β) : forIn [] b f = pure b :=
  rfl

instance : ForM m (List α) α where
  forM := List.forM

@[simp] theorem forM_nil  [Monad m] (f : α → m PUnit) : forM [] f = pure ⟨⟩ :=
  rfl
@[simp] theorem forM_cons [Monad m] (f : α → m PUnit) (a : α) (as : List α) : forM (a::as) f = f a >>= fun _ => forM as f :=
  rfl

instance : Functor List where
  map := List.map

end List
