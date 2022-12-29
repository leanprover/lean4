/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Basic
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

@[inline]
def mapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) (as : List α) : m (List β) :=
  let rec @[specialize] loop
    | [],      bs => pure bs.reverse
    | a :: as, bs => do loop as ((← f a)::bs)
  loop as []

@[specialize]
def mapA {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
  | []    => pure []
  | a::as => List.cons <$> f a <*> mapA f as

@[specialize]
protected def forM {m : Type u → Type v} [Monad m] {α : Type w} (as : List α) (f : α → m PUnit) : m PUnit :=
  match as with
  | []      => pure ⟨⟩
  | a :: as => do f a; List.forM as f

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

@[inline]
def filterM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) (as : List α) : m (List α) := do
  let as ← filterAuxM f as []
  pure as.reverse

@[inline]
def filterRevM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) (as : List α) : m (List α) :=
  filterAuxM f as.reverse []

@[inline]
def filterMapM {m : Type u → Type v} [Monad m] {α β : Type u} (f : α → m (Option β)) (as : List α) : m (List β) :=
  let rec @[specialize] loop
    | [],     bs => pure bs
    | a :: as, bs => do
      match (← f a) with
      | none   => loop as bs
      | some b => loop as (b::bs)
  loop as.reverse []

@[specialize]
protected def foldlM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (f : s → α → m s) → (init : s) → List α → m s
  | _, s, []      => pure s
  | f, s, a :: as => do
    let s' ← f s a
    List.foldlM f s' as

@[inline]
def foldrM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} (f : α → s → m s) (init : s) (l : List α) : m s :=
  l.reverse.foldlM (fun s a => f a s) init

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

@[specialize]
def findSomeM? {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m (Option β)) : List α → m (Option β)
  | []    => pure none
  | a::as => do
    match (← f a) with
    | some b => pure (some b)
    | none   => findSomeM? f as

@[inline] protected def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : List α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop
    | [], b    => pure b
    | a::as, b => do
      match (← f a b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop as b
  loop as init

instance : ForIn m (List α) α where
  forIn := List.forIn

@[simp] theorem forIn_nil [Monad m] (f : α → β → m (ForInStep β)) (b : β) : forIn [] b f = pure b :=
  rfl

@[simp] theorem forIn_cons [Monad m] (f : α → β → m (ForInStep β)) (a : α) (as : List α) (b : β)
    : forIn (a::as) b f = f a b >>= fun | ForInStep.done b => pure b | ForInStep.yield b => forIn as b f :=
  rfl

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

@[simp] theorem forIn'_eq_forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : List α) (init : β) (f : α → β → m (ForInStep β)) : forIn' as init (fun a _ b => f a b) = forIn as init f := by
  simp [forIn', forIn, List.forIn, List.forIn']
  have : ∀ cs h, List.forIn'.loop cs (fun a _ b => f a b) as init h = List.forIn.loop f as init := by
    intro cs h
    induction as generalizing cs init with
    | nil => intros; rfl
    | cons a as ih => intros; simp [List.forIn.loop, List.forIn'.loop, ih]
  apply this

instance : ForM m (List α) α where
  forM := List.forM

@[simp] theorem forM_nil  [Monad m] (f : α → m PUnit) : forM [] f = pure ⟨⟩ :=
  rfl
@[simp] theorem forM_cons [Monad m] (f : α → m PUnit) (a : α) (as : List α) : forM (a::as) f = f a >>= fun _ => forM as f :=
  rfl

instance : Functor List where
  map := List.map

end List
