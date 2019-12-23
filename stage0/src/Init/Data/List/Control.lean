/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Monad
import Init.Control.Alternative
import Init.Data.List.Basic

namespace List
universes u v w u₁ u₂

/-
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

@[specialize]
def mapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
| []    => pure []
| a::as => do b ← f a; bs ← mapM as; pure (b :: bs)

@[specialize]
def mapM₂ {m : Type u → Type v} [Monad m] {α : Type u₁} {β : Type u₂} {γ : Type u} (f : α → β → m γ) : List α → List β → m (List γ)
| a::as, b::bs => do c ← f a b; cs ← mapM₂ as bs; pure (c :: cs)
| _,     _     => pure []

@[specialize]
def mapA {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
| []    => pure []
| a::as => List.cons <$> f a <*> mapA as

@[specialize]
def mapA₂ {m : Type u → Type v} [Applicative m] {α : Type u₁} {β : Type u₂} {γ : Type u} (f : α → β → m γ) : List α → List β → m (List γ)
| a::as, b::bs => List.cons <$> f a b <*> mapA₂ as bs
| _,     _     => pure []

@[specialize]
def forM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) : List α → m PUnit
| []     => pure ⟨⟩
| h :: t => do f h; forM t

@[specialize]
def forM₂ {m : Type u → Type v} [Monad m] {α : Type u₁} {β : Type u₂} {γ : Type u} (f : α → β → m γ) : List α → List β → m PUnit
| a::as, b::bs => do f a b; forM₂ as bs
| _,     _     => pure ⟨⟩

@[specialize]
def forA {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m PUnit
| []     => pure ⟨⟩
| h :: t => f h *> forA t

@[specialize]
def forA₂ {m : Type u → Type v} [Applicative m] {α : Type u₁} {β : Type u₂} {γ : Type u} (f : α → β → m γ) : List α → List β → m PUnit
| a::as, b::bs => f a b *> forA₂ as bs
| _,     _     => pure ⟨⟩

@[specialize]
def filterAuxM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → List α → m (List α)
| [],     acc => pure acc
| h :: t, acc => do b ← f h; filterAuxM t (cond b (h :: acc) acc)

@[inline]
def filterM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) (as : List α) : m (List α) :=
do as ← filterAuxM f as []; pure as.reverse

@[inline]
def filterRevM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) (as : List α) : m (List α) :=
filterAuxM f as.reverse []

@[specialize]
def foldlM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → List α → m s
| f, s, [] => pure s
| f, s, h :: r   => do
  s' ← f s h;
  foldlM f s' r

@[specialize]
def foldrM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (α → s → m s) → s → List α → m s
| f, s, [] => pure s
| f, s, h :: r   => do
  s' ← foldrM f s r;
  f h s'

@[specialize]
def firstM {m : Type u → Type v} [Monad m] [Alternative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m β
| []    => failure
| a::as => f a <|> firstM as

@[specialize]
def anyM {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []    => pure false
| a::as => do b ← f a; match b with
  | true  => pure true
  | false =>  anyM as

@[specialize]
def allM {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []    => pure true
| a::as => do b ← f a; match b with
  | true  => allM as
  | false => pure false

end List
