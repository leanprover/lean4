/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
module

prelude
public meta import Init.Prelude
public import Init.SizeOf

public section
set_option linter.missingDocs true -- keep it documented

@[expose] section

universe u v w

/--
`inline (f x)` is an indication to the compiler to inline the definition of `f`
at the application site itself (by comparison to the `@[inline]` attribute,
which applies to all applications of the function).
-/
@[simp] def inline {α : Sort u} (a : α) : α := a

theorem id_def {α : Sort u} (a : α) : id a = a := rfl

attribute [grind] id

/--
A helper gadget for instructing the kernel to eagerly reduce terms.

When the gadget wraps the argument of an application, then when checking that
the expected and inferred type of the argument match, the kernel will evaluate terms more eagerly.
It is often used to wrap `Eq.refl true` proof terms as `eagerReduce (Eq.refl true)`
when using proof by reflection.
As an example, consider the theorem:
```
theorem eq_norm (ctx : Context) (p₁ p₂ : Poly) (h : (p₁.norm == p₂) = true) :
  p₁.denote ctx = 0 → p₂.denote ctx = 0
```
The argument `h : (p₁.norm == p₂) = true` is a candidate for `eagerReduce`.
When applying this theorem, we would write:

```
eq_norm ctx p q (eagerReduce (Eq.refl true)) h
```
to instruct the kernel to use eager reduction when establishing that `(p.norm == q) = true` is
definitionally equal to `true = true`.
-/
@[expose] def eagerReduce {α : Sort u} (a : α) : α := a

/--
`flip f a b` is `f b a`. It is useful for "point-free" programming,
since it can sometimes be used to avoid introducing variables.
For example, `(·<·)` is the less-than relation,
and `flip (·<·)` is the greater-than relation.
-/
@[inline] def flip {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) : β → α → φ :=
  fun b a => f a b

@[simp] theorem Function.const_apply {y : β} {x : α} : const α y x = y := rfl

@[simp] theorem Function.comp_apply {f : β → δ} {g : α → β} {x : α} : comp f g x = f (g x) := rfl

theorem Function.comp_def {α β δ} (f : β → δ) (g : α → β) : f ∘ g = fun x => f (g x) := rfl

@[simp] theorem Function.const_comp {f : α → β} {c : γ} :
    (Function.const β c ∘ f) = Function.const α c :=
  rfl
@[simp] theorem Function.comp_const {f : β → γ} {b : β} :
    (f ∘ Function.const α b) = Function.const α (f b) :=
  rfl
@[simp] theorem Function.true_comp {f : α → β} : ((fun _ => true) ∘ f) = fun _ => true :=
  rfl
@[simp] theorem Function.false_comp {f : α → β} : ((fun _ => false) ∘ f) = fun _ => false :=
  rfl

@[simp] theorem Function.comp_id (f : α → β) : f ∘ id = f := rfl
@[simp] theorem Function.id_comp (f : α → β) : id ∘ f = f := rfl

attribute [simp] namedPattern

/--
`Empty.elim : Empty → C` says that a value of any type can be constructed from
`Empty`. This can be thought of as a compiler-checked assertion that a code path is unreachable.
-/
@[macro_inline] def Empty.elim {C : Sort u} : Empty → C := Empty.rec

/-- Decidable equality for Empty -/
instance : DecidableEq Empty := fun a => a.elim

/--
`PEmpty.elim : Empty → C` says that a value of any type can be constructed from
`PEmpty`. This can be thought of as a compiler-checked assertion that a code path is unreachable.
-/
@[macro_inline] def PEmpty.elim {C : Sort _} : PEmpty → C := fun a => nomatch a

/-- Decidable equality for PEmpty -/
instance : DecidableEq PEmpty := fun a => a.elim

set_option genInjectivity false in
/--
Delays evaluation. The delayed code is evaluated at most once.

A thunk is code that constructs a value when it is requested via `Thunk.get`, `Thunk.map`, or
`Thunk.bind`. The resulting value is cached, so the code is executed at most once. This is also
known as lazy or call-by-need evaluation.

The Lean runtime has special support for the `Thunk` type in order to implement the caching
behavior.
-/
structure Thunk (α : Type u) : Type u where
  /--
  Constructs a new thunk from a function `Unit → α` that will be called when the thunk is first
  forced.

  The result is cached. It is re-used when the thunk is forced again.
  -/
  mk ::
  /-- Extract the getter function out of a thunk. Use `Thunk.get` instead. -/
  -- The field is public so as to allow computation through it.
  fn : Unit → α

attribute [extern "lean_mk_thunk"] Thunk.mk

/--
Stores an already-computed value in a thunk.

Because the value has already been computed, there is no laziness.
-/
@[extern "lean_thunk_pure"] protected def Thunk.pure (a : α) : Thunk α :=
  ⟨fun _ => a⟩

/--
Gets the thunk's value. If the value is cached, it is returned in constant time; if not, it is
computed.

Computed values are cached, so the value is not recomputed.
-/
-- NOTE: we use `Thunk.get` instead of `Thunk.fn` as the accessor primitive as the latter has an additional `Unit` argument
@[extern "lean_thunk_get_own"] protected def Thunk.get (x : @& Thunk α) : α :=
  x.fn ()

-- Ensure `Thunk.fn` is still computable even if it shouldn't be accessed directly.
@[inline] private def Thunk.fnImpl (x : Thunk α) : Unit → α := fun _ => x.get
@[csimp] private theorem Thunk.fn_eq_fnImpl : @Thunk.fn = @Thunk.fnImpl := rfl

/--
Constructs a new thunk that forces `x` and then applies `x` to the result. Upon forcing, the result
of `f` is cached and the reference to the thunk `x` is dropped.
-/
@[inline] protected def Thunk.map (f : α → β) (x : Thunk α) : Thunk β :=
  ⟨fun _ => f x.get⟩

/--
Constructs a new thunk that applies `f` to the result of `x` when forced.
-/
@[inline] protected def Thunk.bind (x : Thunk α) (f : α → Thunk β) : Thunk β :=
  ⟨fun _ => (f x.get).get⟩

@[simp] theorem Thunk.sizeOf_eq [SizeOf α] (a : Thunk α) : sizeOf a = 1 + sizeOf a.get := by
   cases a; rfl

instance thunkCoe : CoeTail α (Thunk α) where
  -- Since coercions are expanded eagerly, `a` is evaluated lazily.
  coe a := ⟨fun _ => a⟩

/-- A variation on `Eq.ndrec` with the equality argument first. -/
abbrev Eq.ndrecOn.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} {b : α} (h : a = b) (m : motive a) : motive b :=
  Eq.ndrec m h

/-! # definitions  -/

/--
If and only if, or logical bi-implication. `a ↔ b` means that `a` implies `b` and vice versa.
By `propext`, this implies that `a` and `b` are equal and hence any expression involving `a`
is equivalent to the corresponding expression with `b` instead.
-/
structure Iff (a b : Prop) : Prop where
  /-- If `a → b` and `b → a` then `a` and `b` are equivalent. -/
  intro ::
  /-- Modus ponens for if and only if. If `a ↔ b` and `a`, then `b`. -/
  mp : a → b
  /-- Modus ponens for if and only if, reversed. If `a ↔ b` and `b`, then `a`. -/
  mpr : b → a

@[inherit_doc] infix:20 " <-> " => Iff
@[inherit_doc] infix:20 " ↔ "   => Iff

recommended_spelling "iff" for "↔" in [Iff, «term_↔_»]
/-- prefer `↔` over `<->` -/
recommended_spelling "iff" for "<->" in [Iff, «term_<->_»]

/--
The disjoint union of types `α` and `β`, ordinarily written `α ⊕ β`.

An element of `α ⊕ β` is either an `a : α` wrapped in `Sum.inl` or a `b : β` wrapped in `Sum.inr`.
`α ⊕ β` is not equivalent to the set-theoretic union of `α` and `β` because its values include an
indication of which of the two types was chosen. The union of a singleton set with itself contains
one element, while `Unit ⊕ Unit` contains distinct values `inl ()` and `inr ()`.
-/
inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. -/
  | inr (val : β) : Sum α β

@[inherit_doc] infixr:30 " ⊕ " => Sum

/--
The disjoint union of arbitrary sorts `α` `β`, or `α ⊕' β`.

It differs from `α ⊕ β` in that it allows `α` and `β` to have arbitrary sorts `Sort u` and `Sort v`,
instead of restricting them to `Type u` and `Type v`. This means that it can be used in situations
where one side is a proposition, like `True ⊕' Nat`. However, the resulting universe level
constraints are often more difficult to solve than those that result from `Sum`.
-/
inductive PSum (α : Sort u) (β : Sort v) where
  /-- Left injection into the sum type `α ⊕' β`.-/
  | inl (val : α) : PSum α β
  /-- Right injection into the sum type `α ⊕' β`. -/
  | inr (val : β) : PSum α β

@[inherit_doc] infixr:30 " ⊕' " => PSum

/--
If the left type in a sum is inhabited then the sum is inhabited.

This is not an instance to avoid non-canonical instances when both the left and right types are
inhabited.
-/
@[reducible] def PSum.inhabitedLeft {α β} [Inhabited α] : Inhabited (PSum α β) := ⟨PSum.inl default⟩

/--
If the right type in a sum is inhabited then the sum is inhabited.

This is not an instance to avoid non-canonical instances when both the left and right types are
inhabited.
-/
@[reducible] def PSum.inhabitedRight {α β} [Inhabited β] : Inhabited (PSum α β) := ⟨PSum.inr default⟩

instance PSum.nonemptyLeft [h : Nonempty α] : Nonempty (PSum α β) :=
  Nonempty.elim h (fun a => ⟨PSum.inl a⟩)

instance PSum.nonemptyRight [h : Nonempty β] : Nonempty (PSum α β) :=
  Nonempty.elim h (fun b => ⟨PSum.inr b⟩)

/--
Dependent pairs, in which the second element's type depends on the value of the first element. The
type `Sigma β` is typically written `Σ a : α, β a` or `(a : α) × β a`.

Although its values are pairs, `Sigma` is sometimes known as the *dependent sum type*, since it is
the type level version of an indexed summation.
-/
@[pp_using_anonymous_constructor]
structure Sigma {α : Type u} (β : α → Type v) where
  /--
  Constructs a dependent pair.

  Using this constructor in a context in which the type is not known usually requires a type
  ascription to determine `β`. This is because the desired relationship between the two values can't
  generally be determined automatically.
  -/
  mk ::
  /--
  The first component of a dependent pair.
  -/
  fst : α
  /--
  The second component of a dependent pair. Its type depends on the first component.
  -/
  snd : β fst

attribute [unbox] Sigma

/--
Fully universe-polymorphic dependent pairs, in which the second element's type depends on the value
of the first element and both types are allowed to be propositions. The type `PSigma β` is typically
written `Σ' a : α, β a` or `(a : α) ×' β a`.

In practice, this generality leads to universe level constraints that are difficult to solve, so
`PSigma` is rarely used in manually-written code. It is usually only used in automation that
constructs pairs of arbitrary types.

To pair a value with a proof that a predicate holds for it, use `Subtype`. To demonstrate that a
value exists that satisfies a predicate, use `Exists`. A dependent pair with a proposition as its
first component is not typically useful due to proof irrelevance: there's no point in depending on a
specific proof because all proofs are equal anyway.
-/
@[pp_using_anonymous_constructor]
structure PSigma {α : Sort u} (β : α → Sort v) where
  /-- Constructs a fully universe-polymorphic dependent pair. -/
  mk ::
  /--
  The first component of a dependent pair.
  -/
  fst : α
  /--
  The second component of a dependent pair. Its type depends on the first component.
  -/
  snd : β fst

/--
Existential quantification. If `p : α → Prop` is a predicate, then `∃ x : α, p x`
asserts that there is some `x` of type `α` such that `p x` holds.
To create an existential proof, use the `exists` tactic,
or the anonymous constructor notation `⟨x, h⟩`.
To unpack an existential, use `cases h` where `h` is a proof of `∃ x : α, p x`,
or `let ⟨x, hx⟩ := h` where `.

Because Lean has proof irrelevance, any two proofs of an existential are
definitionally equal. One consequence of this is that it is impossible to recover the
witness of an existential from the mere fact of its existence.
For example, the following does not compile:
```
example (h : ∃ x : Nat, x = x) : Nat :=
  let ⟨x, _⟩ := h  -- fail, because the goal is `Nat : Type`
  x
```
The error message `recursor 'Exists.casesOn' can only eliminate into Prop` means
that this only works when the current goal is another proposition:
```
example (h : ∃ x : Nat, x = x) : True :=
  let ⟨x, _⟩ := h  -- ok, because the goal is `True : Prop`
  trivial
```
-/
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  /-- Existential introduction. If `a : α` and `h : p a`,
  then `⟨a, h⟩` is a proof that `∃ x : α, p x`. -/
  | intro (w : α) (h : p w) : Exists p

/--
An indication of whether a loop's body terminated early that's used to compile the `for x in xs`
notation.

A collection's `ForIn` or `ForIn'` instance describe's how to iterate over its elements. The monadic
action that represents the body of the loop returns a `ForInStep α`, where `α` is the local state
used to implement features such as `let mut`.
-/
inductive ForInStep (α : Type u) where
  /--
  The loop should terminate early.

  `ForInStep.done` is produced by uses of `break` or `return` in the loop body.
  -/
  | done  : α → ForInStep α
  /--
  The loop should continue with the next iteration, using the returned state.

  `ForInStep.yield` is produced by `continue` and by reaching the bottom of the loop body.
  -/
  | yield : α → ForInStep α
  deriving Inhabited

/--
Monadic iteration in `do`-blocks, using the `for x in xs` notation.

The parameter `m` is the monad of the `do`-block in which iteration is performed, `ρ` is the type of
the collection being iterated over, and `α` is the type of elements.
-/
class ForIn (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination.

  Because a `do` block supports local mutable bindings along with `return`, and `break`, the monadic
  action passed to `ForIn.forIn` takes a starting state in addition to the current element of the
  collection and returns an updated state together with an indication of whether iteration should
  continue or terminate. If the action returns `ForInStep.done`, then `ForIn.forIn` should stop
  iteration and return the updated state. If the action returns `ForInStep.yield`, then
  `ForIn.forIn` should continue iterating if there are further elements, passing the updated state
  to the action.

  More information about the translation of `for` loops into `ForIn.forIn` is available in [the Lean
  reference manual](lean-manual://section/monad-iteration-syntax).
  -/
  forIn {β} [Monad m] (xs : ρ) (b : β) (f : α → β → m (ForInStep β)) : m β

export ForIn (forIn)

/--
Monadic iteration in `do`-blocks with a membership proof, using the `for h : x in xs` notation.

The parameter `m` is the monad of the `do`-block in which iteration is performed, `ρ` is the type of
the collection being iterated over, `α` is the type of elements, and `d` is the specific membership
predicate to provide.
-/
class ForIn' (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) (d : outParam (Membership α ρ)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination. At each iteration, the body of the loop is provided with a proof
  that the current element is in the collection.

  Because a `do` block supports local mutable bindings along with `return`, and `break`, the monadic
  action passed to `ForIn'.forIn'` takes a starting state in addition to the current element of the
  collection with its membership proof. The action returns an updated state together with an
  indication of whether iteration should continue or terminate. If the action returns
  `ForInStep.done`, then `ForIn'.forIn'` should stop iteration and return the updated state. If the
  action returns `ForInStep.yield`, then `ForIn'.forIn'` should continue iterating if there are
  further elements, passing the updated state to the action.

  More information about the translation of `for` loops into `ForIn'.forIn'` is available in [the
  Lean reference manual](lean-manual://section/monad-iteration-syntax).
  -/
  forIn' {β} [Monad m] (x : ρ) (b : β) (f : (a : α) → a ∈ x → β → m (ForInStep β)) : m β

export ForIn' (forIn')

/--
Auxiliary type used to compile `do` notation. It is used when compiling a do block
nested inside a combinator like `tryCatch`. It encodes the possible ways the
block can exit:
* `pure (a : α) s` means that the block exited normally with return value `a`.
* `return (b : β) s` means that the block exited via a `return b` early-exit command.
* `break s` means that `break` was called, meaning that we should exit
  from the containing loop.
* `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop.

All cases return a value `s : σ` which bundles all the mutable variables of the do-block.
-/
inductive DoResultPRBC (α β σ : Type u) where
  /-- `pure (a : α) s` means that the block exited normally with return value `a` -/
  | pure : α → σ → DoResultPRBC α β σ
  /-- `return (b : β) s` means that the block exited via a `return b` early-exit command -/
  | return : β → σ → DoResultPRBC α β σ
  /-- `break s` means that `break` was called, meaning that we should exit
  from the containing loop -/
  | break : σ → DoResultPRBC α β σ
  /-- `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop -/
  | continue : σ → DoResultPRBC α β σ

/--
Auxiliary type used to compile `do` notation. It is the same as
`DoResultPRBC α β σ` except that `break` and `continue` are not available
because we are not in a loop context.
-/
inductive DoResultPR (α β σ : Type u) where
  /-- `pure (a : α) s` means that the block exited normally with return value `a` -/
  | pure   : α → σ → DoResultPR α β σ
  /-- `return (b : β) s` means that the block exited via a `return b` early-exit command -/
  | return : β → σ → DoResultPR α β σ

/--
Auxiliary type used to compile `do` notation. It is an optimization of
`DoResultPRBC PEmpty PEmpty σ` to remove the impossible cases,
used when neither `pure` nor `return` are possible exit paths.
-/
inductive DoResultBC (σ : Type u) where
  /-- `break s` means that `break` was called, meaning that we should exit
  from the containing loop -/
  | break    : σ → DoResultBC σ
  /-- `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop -/
  | continue : σ → DoResultBC σ

/--
Auxiliary type used to compile `do` notation. It is an optimization of
either `DoResultPRBC α PEmpty σ` or `DoResultPRBC PEmpty α σ` to remove the
impossible case, used when either `pure` or `return` is never used.
-/
inductive DoResultSBC (α σ : Type u) where
  /-- This encodes either `pure (a : α)` or `return (a : α)`:
  * `pure (a : α) s` means that the block exited normally with return value `a`
  * `return (b : β) s` means that the block exited via a `return b` early-exit command

  The one that is actually encoded depends on the context of use. -/
  | pureReturn : α → σ → DoResultSBC α σ
  /-- `break s` means that `break` was called, meaning that we should exit
  from the containing loop -/
  | break    : σ → DoResultSBC α σ
  /-- `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop -/
  | continue   : σ → DoResultSBC α σ

/-- `HasEquiv α` is the typeclass which supports the notation `x ≈ y` where `x y : α`.-/
class HasEquiv (α : Sort u) where
  /-- `x ≈ y` says that `x` and `y` are equivalent. Because this is a typeclass,
  the notion of equivalence is type-dependent. -/
  Equiv : α → α → Sort v

@[inherit_doc] infix:50 " ≈ "  => HasEquiv.Equiv

recommended_spelling "equiv" for "≈" in [HasEquiv.Equiv, «term_≈_»]

/-! # set notation  -/

/-- Notation type class for the subset relation `⊆`. -/
class HasSubset (α : Type u) where
  /-- Subset relation: `a ⊆ b`  -/
  Subset : α → α → Prop
export HasSubset (Subset)

/-- Notation type class for the strict subset relation `⊂`. -/
class HasSSubset (α : Type u) where
  /-- Strict subset relation: `a ⊂ b`  -/
  SSubset : α → α → Prop
export HasSSubset (SSubset)

/-- Superset relation: `a ⊇ b`  -/
abbrev Superset [HasSubset α] (a b : α) := Subset b a

/-- Strict superset relation: `a ⊃ b`  -/
abbrev SSuperset [HasSSubset α] (a b : α) := SSubset b a

/-- Notation type class for the union operation `∪`. -/
class Union (α : Type u) where
  /-- `a ∪ b` is the union of`a` and `b`. -/
  union : α → α → α

/-- Notation type class for the intersection operation `∩`. -/
class Inter (α : Type u) where
  /-- `a ∩ b` is the intersection of`a` and `b`. -/
  inter : α → α → α

/-- Notation type class for the set difference `\`. -/
class SDiff (α : Type u) where
  /--
  `a \ b` is the set difference of `a` and `b`,
  consisting of all elements in `a` that are not in `b`.
  -/
  sdiff : α → α → α

/-- Subset relation: `a ⊆ b`  -/
infix:50 " ⊆ " => Subset

/-- Strict subset relation: `a ⊂ b`  -/
infix:50 " ⊂ " => SSubset

/-- Superset relation: `a ⊇ b`  -/
infix:50 " ⊇ " => Superset

/-- Strict superset relation: `a ⊃ b`  -/
infix:50 " ⊃ " => SSuperset

/-- `a ∪ b` is the union of`a` and `b`. -/
infixl:65 " ∪ " => Union.union

/-- `a ∩ b` is the intersection of`a` and `b`. -/
infixl:70 " ∩ " => Inter.inter

/--
`a \ b` is the set difference of `a` and `b`,
consisting of all elements in `a` that are not in `b`.
-/
infix:70 " \\ " => SDiff.sdiff

recommended_spelling "subset" for "⊆" in [Subset, «term_⊆_»]
recommended_spelling "ssubset" for "⊂" in [SSubset, «term_⊂_»]
/-- prefer `⊆` over `⊇` -/
recommended_spelling "superset" for "⊇" in [Superset, «term_⊇_»]
/-- prefer `⊂` over `⊃` -/
recommended_spelling "ssuperset" for "⊃" in [SSuperset, «term_⊃_»]
recommended_spelling "union" for "∪" in [Union.union, «term_∪_»]
recommended_spelling "inter" for "∩" in [Inter.inter, «term_∩_»]
recommended_spelling "sdiff" for "\\" in [SDiff.sdiff, «term_\_»]

/-! # collections  -/

/-- `EmptyCollection α` is the typeclass which supports the notation `∅`, also written as `{}`. -/
class EmptyCollection (α : Type u) where
  /-- `∅` or `{}` is the empty set or empty collection.
  It is supported by the `EmptyCollection` typeclass. -/
  emptyCollection : α

@[inherit_doc] notation "{" "}" => EmptyCollection.emptyCollection
@[inherit_doc] notation "∅"     => EmptyCollection.emptyCollection

recommended_spelling "empty" for "{}" in [EmptyCollection.emptyCollection, «term{}»]
recommended_spelling "empty" for "∅" in [EmptyCollection.emptyCollection, «term∅»]

/--
Type class for the `insert` operation.
Used to implement the `{ a, b, c }` syntax.
-/
class Insert (α : outParam <| Type u) (γ : Type v) where
  /-- `insert x xs` inserts the element `x` into the collection `xs`. -/
  insert : α → γ → γ
export Insert (insert)

/--
Type class for the `singleton` operation.
Used to implement the `{ a, b, c }` syntax.
-/
class Singleton (α : outParam <| Type u) (β : Type v) where
  /-- `singleton x` is a collection with the single element `x` (notation: `{x}`). -/
  singleton : α → β
export Singleton (singleton)

/-- `insert x ∅ = {x}` -/
class LawfulSingleton (α : Type u) (β : Type v) [EmptyCollection β] [Insert α β] [Singleton α β] :
    Prop where
  /-- `insert x ∅ = {x}` -/
  insert_empty_eq (x : α) : (insert x ∅ : β) = singleton x
export LawfulSingleton (insert_empty_eq)

attribute [simp] insert_empty_eq

@[deprecated insert_empty_eq (since := "2025-03-12")]
theorem insert_emptyc_eq [EmptyCollection β] [Insert α β] [Singleton α β]
    [LawfulSingleton α β] (x : α) : (insert x ∅ : β) = singleton x :=
  insert_empty_eq _

@[deprecated insert_empty_eq (since := "2025-03-12")]
theorem LawfulSingleton.insert_emptyc_eq [EmptyCollection β] [Insert α β] [Singleton α β]
    [LawfulSingleton α β] (x : α) : (insert x ∅ : β) = singleton x :=
  insert_empty_eq _


/-- Type class used to implement the notation `{ a ∈ c | p a }` -/
class Sep (α : outParam <| Type u) (γ : Type v) where
  /-- Computes `{ a ∈ c | p a }`. -/
  sep : (α → Prop) → γ → γ

set_option genInjectivity false in
/--
`Task α` is a primitive for asynchronous computation.
It represents a computation that will resolve to a value of type `α`,
possibly being computed on another thread. This is similar to `Future` in Scala,
`Promise` in Javascript, and `JoinHandle` in Rust.

The tasks have an overridden representation in the runtime.
-/
structure Task (α : Type u) : Type u where
  /-- `Task.pure (a : α)` constructs a task that is already resolved with value `a`. -/
  pure ::
  /--
  Blocks the current thread until the given task has finished execution, and then returns the result
  of the task. If the current thread is itself executing a (non-dedicated) task, the maximum
  threadpool size is temporarily increased by one while waiting so as to ensure the process cannot
  be deadlocked by threadpool starvation. Note that when the current thread is unblocked, more tasks
  than the configured threadpool size may temporarily be running at the same time until sufficiently
  many tasks have finished.

  `Task.map` and `Task.bind` should be preferred over `Task.get` for setting up task dependencies
  where possible as they do not require temporarily growing the threadpool in this way. In
  particular, calling `Task.get` in a task continuation with `(sync := true)` will panic as the
  continuation is decidedly not "cheap" in this case and deadlocks may otherwise occur. The
  waited-upon task should instead be returned and unwrapped using `Task.bind/IO.bindTask`.
  -/
  get : α
  deriving Inhabited, Nonempty

attribute [extern "lean_task_pure"] Task.pure
attribute [extern "lean_task_get_own"] Task.get

namespace Task
/--
Task priority.

Tasks with higher priority will always be scheduled before tasks with lower priority. Tasks with a
priority greater than `Task.Priority.max` are scheduled on dedicated threads.
-/
abbrev Priority := Nat

/-- The default priority for spawned tasks, also the lowest priority: `0`. -/
def Priority.default : Priority := 0
/--
The highest regular priority for spawned tasks: `8`.

Spawning a task with a priority higher than `Task.Priority.max` is not an error but will spawn a
dedicated worker for the task. This is indicated using `Task.Priority.dedicated`. Regular priority
tasks are placed in a thread pool and worked on according to their priority order.
-/
-- see `LEAN_MAX_PRIO`
def Priority.max : Priority := 8
/--
Indicates that a task should be scheduled on a dedicated thread.

Any priority higher than `Task.Priority.max` will result in the task being scheduled
immediately on a dedicated thread. This is particularly useful for long-running and/or
I/O-bound tasks since Lean will, by default, allocate no more non-dedicated workers
than the number of cores to reduce context switches.
-/
def Priority.dedicated : Priority := 9

set_option linter.unusedVariables.funArgs false in
/--
`spawn fn : Task α` constructs and immediately launches a new task for
evaluating the function `fn () : α` asynchronously.

`prio`, if provided, is the priority of the task.
-/
@[noinline, extern "lean_task_spawn"]
protected def spawn {α : Type u} (fn : Unit → α) (prio := Priority.default) : Task α :=
  ⟨fn ()⟩

set_option linter.unusedVariables.funArgs false in
/--
`map f x` maps function `f` over the task `x`: that is, it constructs
(and immediately launches) a new task which will wait for the value of `x` to
be available and then calls `f` on the result.

`prio`, if provided, is the priority of the task.
If `sync` is set to true, `f` is executed on the current thread if `x` has already finished and
otherwise on the thread that `x` finished on. `prio` is ignored in this case. This should only be
done when executing `f` is cheap and non-blocking.
-/
@[noinline, extern "lean_task_map"]
protected def map (f : α → β) (x : Task α) (prio := Priority.default) (sync := false) : Task β :=
  ⟨f x.get⟩

set_option linter.unusedVariables.funArgs false in
/--
`bind x f` does a monad "bind" operation on the task `x` with function `f`:
that is, it constructs (and immediately launches) a new task which will wait
for the value of `x` to be available and then calls `f` on the result,
resulting in a new task which is then run for a result.

`prio`, if provided, is the priority of the task.
If `sync` is set to true, `f` is executed on the current thread if `x` has already finished and
otherwise on the thread that `x` finished on. `prio` is ignored in this case. This should only be
done when executing `f` is cheap and non-blocking.
-/
@[noinline, extern "lean_task_bind"]
protected def bind (x : Task α) (f : α → Task β) (prio := Priority.default) (sync := false) :
    Task β :=
  ⟨(f x.get).get⟩

end Task

/--
`NonScalar` is a type that is not a scalar value in our runtime.
It is used as a stand-in for an arbitrary boxed value to avoid excessive
monomorphization, and it is only created using `unsafeCast`. It is somewhat
analogous to C `void*` in usage, but the type itself is not special.
-/
structure NonScalar where
  /-- You should not use this function -/ mk ::
  /-- You should not use this function -/ val : Nat

/--
`PNonScalar` is a type that is not a scalar value in our runtime.
It is used as a stand-in for an arbitrary boxed value to avoid excessive
monomorphization, and it is only created using `unsafeCast`. It is somewhat
analogous to C `void*` in usage, but the type itself is not special.

This is the universe-polymorphic version of `PNonScalar`; it is preferred to use
`NonScalar` instead where applicable.
-/
inductive PNonScalar : Type u where
  /-- You should not use this function -/
  | mk (v : Nat) : PNonScalar

@[simp] protected theorem Nat.add_zero (n : Nat) : n + 0 = n := rfl

theorem optParam_eq (α : Sort u) (default : α) : optParam α default = α := rfl

/-! # Boolean operators -/

/--
`strictOr` is the same as `or`, but it does not use short-circuit evaluation semantics:
both sides are evaluated, even if the first value is `true`.
-/
@[extern "lean_strict_or"] def strictOr  (b₁ b₂ : Bool) := b₁ || b₂

/--
`strictAnd` is the same as `and`, but it does not use short-circuit evaluation semantics:
both sides are evaluated, even if the first value is `false`.
-/
@[extern "lean_strict_and"] def strictAnd (b₁ b₂ : Bool) := b₁ && b₂

/--
`x != y` is boolean not-equal. It is the negation of `x == y` which is supplied by
the `BEq` typeclass.

Unlike `x ≠ y` (which is notation for `Ne x y`), this is `Bool` valued instead of
`Prop` valued. It is mainly intended for programming applications.
-/
@[inline] def bne {α : Type u} [BEq α] (a b : α) : Bool :=
  !(a == b)

@[inherit_doc] infix:50 " != " => bne

macro_rules | `($x != $y) => `(binrel_no_prop% bne $x $y)

recommended_spelling "bne" for "!=" in [bne, «term_!=_»]

/-- `ReflBEq α` says that the `BEq` implementation is reflexive. -/
class ReflBEq (α) [BEq α] : Prop where
  /-- `==` is reflexive, that is, `(a == a) = true`. -/
  protected rfl {a : α} : a == a

@[simp] theorem BEq.rfl [BEq α] [ReflBEq α] {a : α} : a == a := ReflBEq.rfl
theorem BEq.refl [BEq α] [ReflBEq α] (a : α) : a == a := BEq.rfl

theorem beq_of_eq [BEq α] [ReflBEq α] {a b : α} : a = b → a == b
  | rfl => BEq.rfl

theorem not_eq_of_beq_eq_false [BEq α] [ReflBEq α] {a b : α} (h : (a == b) = false) : ¬a = b := by
  intro h'; subst h'; have : true = false := BEq.rfl.symm.trans h; contradiction

/--
A Boolean equality test coincides with propositional equality.

In other words:
 * `a == b` implies `a = b`.
 * `a == a` is true.
-/
class LawfulBEq (α : Type u) [BEq α] : Prop extends ReflBEq α where
  /-- If `a == b` evaluates to `true`, then `a` and `b` are equal in the logic. -/
  eq_of_beq : {a b : α} → a == b → a = b

export LawfulBEq (eq_of_beq)

instance : LawfulBEq Bool where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> decide

instance [DecidableEq α] : LawfulBEq α where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

/--
Non-instance for `DecidableEq` from `LawfulBEq`.
To use this, add `attribute [local instance 5] instDecidableEqOfLawfulBEq` at the top of a file.
-/
def instDecidableEqOfLawfulBEq [BEq α] [LawfulBEq α] : DecidableEq α := fun x y =>
  match h : x == y with
  | false => .isFalse (not_eq_of_beq_eq_false h)
  | true => .isTrue (eq_of_beq h)

instance : LawfulBEq Char := inferInstance

instance : LawfulBEq String := inferInstance

/-! # Logical connectives and equality -/

@[inherit_doc True.intro] theorem trivial : True := ⟨⟩

theorem mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a :=
  fun ha => h₂ (h₁ ha)

theorem not_false : ¬False := id

theorem not_not_intro {p : Prop} (h : p) : ¬ ¬ p :=
  fun hn : ¬ p => hn h

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (h₁ h₂ : a) : h₁ = h₂ := rfl

/--
If `h : α = β` is a proof of type equality, then `h.mp : α → β` is the induced
"cast" operation, mapping elements of `α` to elements of `β`.

You can prove theorems about the resulting element by induction on `h`, since
`rfl.mp` is definitionally the identity function.
-/
@[macro_inline] def Eq.mp {α β : Sort u} (h : α = β) (a : α) : β :=
  h ▸ a

/--
If `h : α = β` is a proof of type equality, then `h.mpr : β → α` is the induced
"cast" operation in the reverse direction, mapping elements of `β` to elements of `α`.

You can prove theorems about the resulting element by induction on `h`, since
`rfl.mpr` is definitionally the identity function.
-/
@[macro_inline] def Eq.mpr {α β : Sort u} (h : α = β) (b : β) : α :=
  h ▸ b

@[elab_as_elim]
theorem Eq.substr {α : Sort u} {p : α → Prop} {a b : α} (h₁ : b = a) (h₂ : p a) : p b :=
  h₁ ▸ h₂

@[simp] theorem cast_eq {α : Sort u} (h : α = α) (a : α) : cast h a = a :=
  rfl

/--
`a ≠ b`, or `Ne a b` is defined as `¬ (a = b)` or `a = b → False`,
and asserts that `a` and `b` are not equal.
-/
@[reducible] def Ne {α : Sort u} (a b : α) :=
  ¬(a = b)

@[inherit_doc] infix:50 " ≠ "  => Ne

macro_rules | `($x ≠ $y) => `(binrel% Ne $x $y)

recommended_spelling "ne" for "≠" in [Ne, «term_≠_»]

section Ne
variable {α : Sort u}
variable {a b : α} {p : Prop}

theorem Ne.intro (h : a = b → False) : a ≠ b := h

theorem Ne.elim (h : a ≠ b) : a = b → False := h

theorem Ne.irrefl (h : a ≠ a) : False := h rfl

@[symm] theorem Ne.symm (h : a ≠ b) : b ≠ a := fun h₁ => h (h₁.symm)

theorem ne_comm {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨Ne.symm, Ne.symm⟩

theorem false_of_ne : a ≠ a → False := Ne.irrefl

theorem ne_false_of_self : p → p ≠ False :=
  fun (hp : p) (h : p = False) => h ▸ hp

theorem ne_true_of_not : ¬p → p ≠ True :=
  fun (hnp : ¬p) (h : p = True) =>
    have : ¬True := h ▸ hnp
    this trivial

theorem true_ne_false : ¬True = False := ne_false_of_self trivial
theorem false_ne_true : False ≠ True := fun h => h.symm ▸ trivial

end Ne

theorem Bool.of_not_eq_true : {b : Bool} → ¬ (b = true) → b = false
  | true,  h => absurd rfl h
  | false, _ => rfl

theorem Bool.of_not_eq_false : {b : Bool} → ¬ (b = false) → b = true
  | true,  _ => rfl
  | false, h => absurd rfl h

theorem ne_of_beq_false [BEq α] [ReflBEq α] {a b : α} (h : (a == b) = false) : a ≠ b :=
  not_eq_of_beq_eq_false h

theorem beq_false_of_ne [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) : (a == b) = false :=
  have : ¬ (a == b) = true := by
    intro h'; rw [eq_of_beq h'] at h; contradiction
  Bool.of_not_eq_true this

section
variable {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}

/-- Non-dependent recursor for `HEq` -/
noncomputable def HEq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : {β : Sort u2} → β → Sort u1} (m : motive a) {β : Sort u2} {b : β} (h : a ≍ b) : motive b :=
  h.rec m

/-- `HEq.ndrec` variant -/
noncomputable def HEq.ndrecOn.{u1, u2} {α : Sort u2} {a : α} {motive : {β : Sort u2} → β → Sort u1} {β : Sort u2} {b : β} (h : a ≍ b) (m : motive a) : motive b :=
  h.rec m

/-- `HEq.ndrec` variant -/
noncomputable def HEq.elim {α : Sort u} {a : α} {p : α → Sort v} {b : α} (h₁ : a ≍ b) (h₂ : p a) : p b :=
  eq_of_heq h₁ ▸ h₂

/-- Substitution with heterogeneous equality. -/
theorem HEq.subst {p : (T : Sort u) → T → Prop} (h₁ : a ≍ b) (h₂ : p α a) : p β b :=
  HEq.ndrecOn h₁ h₂

/-- Heterogeneous equality is symmetric. -/
@[symm] theorem HEq.symm (h : a ≍ b) : b ≍ a :=
  h.rec (HEq.refl a)

/-- Propositionally equal terms are also heterogeneously equal. -/
theorem heq_of_eq (h : a = a') : a ≍ a' :=
  Eq.subst h (HEq.refl a)

/-- Heterogeneous equality is transitive. -/
theorem HEq.trans (h₁ : a ≍ b) (h₂ : b ≍ c) : a ≍ c :=
  HEq.subst h₂ h₁

/-- Heterogeneous equality precomposes with propositional equality. -/
theorem heq_of_heq_of_eq (h₁ : a ≍ b) (h₂ : b = b') : a ≍ b' :=
  HEq.trans h₁ (heq_of_eq h₂)

/-- Heterogeneous equality postcomposes with propositional equality. -/
theorem heq_of_eq_of_heq (h₁ : a = a') (h₂ : a' ≍ b) : a ≍ b :=
  HEq.trans (heq_of_eq h₁) h₂

/-- If two terms are heterogeneously equal then their types are propositionally equal. -/
theorem type_eq_of_heq (h : a ≍ b) : α = β :=
  h.rec (Eq.refl α)

end

/--
Rewriting inside `φ` using `Eq.recOn` yields a term that's heterogeneously equal to the original
term.
-/
theorem eqRec_heq {α : Sort u} {φ : α → Sort v} {a a' : α} : (h : a = a') → (p : φ a) → Eq.recOn (motive := fun x _ => φ x) h p ≍ p
  | rfl, p => HEq.refl p

/--
Heterogeneous equality with an `Eq.rec` application on the left is equivalent to a heterogeneous
equality on the original term.
-/
theorem eqRec_heq_iff {α : Sort u} {a : α} {motive : (b : α) → a = b → Sort v}
    {b : α} {refl : motive a (Eq.refl a)} {h : a = b} {c : motive b h}
    : @Eq.rec α a motive refl b h ≍ c ↔ refl ≍ c :=
  h.rec (fun _ => ⟨id, id⟩) c

/--
Heterogeneous equality with an `Eq.rec` application on the right is equivalent to a heterogeneous
equality on the original term.
-/
theorem heq_eqRec_iff {α : Sort u} {a : α} {motive : (b : α) → a = b → Sort v}
    {b : α} {refl : motive a (Eq.refl a)} {h : a = b} {c : motive b h} :
    c ≍ @Eq.rec α a motive refl b h ↔ c ≍ refl :=
  h.rec (fun _ => ⟨id, id⟩) c

/--
Moves an cast using `Eq.rec` from the function to the argument.
Note: because the motive isn't reliably detected by unification,
it needs to be provided as an explicit parameter.
-/
theorem apply_eqRec {α : Sort u} {a : α} (motive : (b : α) → a = b → Sort v)
    {b : α} {h : a = b} {c : motive a (Eq.refl a) → β} {d : motive b h} :
    @Eq.rec α a (fun b h => motive b h → β) c b h d = c (h.symm ▸ d) := by
  cases h; rfl

/--
If casting a term with `Eq.rec` to another type makes it equal to some other term, then the two
terms are heterogeneously equal.
-/
theorem heq_of_eqRec_eq {α β : Sort u} {a : α} {b : β} (h₁ : α = β) (h₂ : Eq.rec (motive := fun α _ => α) a h₁ = b) : a ≍ b := by
  subst h₁
  apply heq_of_eq
  exact h₂

/--
The result of casting a term with `cast` is heterogeneously equal to the original term.
-/
theorem cast_heq {α β : Sort u} : (h : α = β) → (a : α) → cast h a ≍ a
  | rfl, a => HEq.refl a

variable {a b c d : Prop}

theorem iff_iff_implies_and_implies {a b : Prop} : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
  Iff.intro (fun h => And.intro h.mp h.mpr) (fun h => Iff.intro h.left h.right)

@[refl] theorem Iff.refl (a : Prop) : a ↔ a :=
  Iff.intro (fun h => h) (fun h => h)

protected theorem Iff.rfl {a : Prop} : a ↔ a :=
  Iff.refl a

-- And, also for backward compatibility, we try `Iff.rfl.` using `exact` (see #5366)
macro_rules | `(tactic| rfl) => `(tactic| exact Iff.rfl)

theorem Iff.of_eq (h : a = b) : a ↔ b := h ▸ Iff.rfl

theorem Iff.trans (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
  Iff.intro (h₂.mp ∘ h₁.mp) (h₁.mpr ∘ h₂.mpr)

-- This is needed for `calc` to work with `iff`.
instance : Trans Iff Iff Iff where
  trans := Iff.trans

theorem Eq.comm {a b : α} : a = b ↔ b = a := Iff.intro Eq.symm Eq.symm
theorem eq_comm {a b : α} : a = b ↔ b = a := Eq.comm

theorem HEq.comm {a : α} {b : β} : a ≍ b ↔ b ≍ a := Iff.intro HEq.symm HEq.symm
theorem heq_comm {a : α} {b : β} : a ≍ b ↔ b ≍ a := HEq.comm

@[symm] theorem Iff.symm (h : a ↔ b) : b ↔ a := Iff.intro h.mpr h.mp
theorem Iff.comm : (a ↔ b) ↔ (b ↔ a) := Iff.intro Iff.symm Iff.symm
theorem iff_comm : (a ↔ b) ↔ (b ↔ a) := Iff.comm

@[symm] theorem And.symm : a ∧ b → b ∧ a := fun ⟨ha, hb⟩ => ⟨hb, ha⟩
theorem And.comm : a ∧ b ↔ b ∧ a := Iff.intro And.symm And.symm
theorem and_comm : a ∧ b ↔ b ∧ a := And.comm

@[symm] theorem Or.symm : a ∨ b → b ∨ a := .rec .inr .inl
theorem Or.comm : a ∨ b ↔ b ∨ a := Iff.intro Or.symm Or.symm
theorem or_comm : a ∨ b ↔ b ∨ a := Or.comm

/-! # Exists -/

theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
   (h₁ : Exists (fun x => p x)) (h₂ : ∀ (a : α), p a → b) : b :=
  match h₁ with
  | intro a h => h₂ a h

/-! # Decidable -/

@[simp] theorem decide_true (h : Decidable True) : @decide True h = true :=
  match h with
  | isTrue _  => rfl
  | isFalse h => False.elim <| h ⟨⟩

@[simp] theorem decide_false (h : Decidable False) : @decide False h = false :=
  match h with
  | isFalse _ => rfl
  | isTrue h  => False.elim h

/-- Similar to `decide`, but uses an explicit instance -/
@[inline] def toBoolUsing {p : Prop} (d : Decidable p) : Bool :=
  decide (h := d)

theorem toBoolUsing_eq_true {p : Prop} (d : Decidable p) (h : p) : toBoolUsing d = true :=
  decide_eq_true (inst := d) h

theorem of_toBoolUsing_eq_true {p : Prop} {d : Decidable p} (h : toBoolUsing d = true) : p :=
  of_decide_eq_true h

theorem of_toBoolUsing_eq_false {p : Prop} {d : Decidable p} (h : toBoolUsing d = false) : ¬p :=
  of_decide_eq_false h

set_option linter.missingDocs false in
@[deprecated of_toBoolUsing_eq_true (since := "2025-04-04")]
abbrev ofBoolUsing_eq_true := @of_toBoolUsing_eq_true

set_option linter.missingDocs false in
@[deprecated of_toBoolUsing_eq_false (since := "2025-04-04")]
abbrev ofBoolUsing_eq_false := @of_toBoolUsing_eq_false

instance : Decidable True :=
  isTrue trivial

instance : Decidable False :=
  isFalse not_false

namespace Decidable
variable {p q : Prop}

/--
Construct a `q` if some proposition `p` is decidable, and both the truth and falsity of `p` are
sufficient to construct a `q`.

This is a synonym for `dite`, the dependent if-then-else operator.
-/
@[macro_inline] def byCases {q : Sort u} [dec : Decidable p] (h1 : p → q) (h2 : ¬p → q) : q :=
  match dec with
  | isTrue h  => h1 h
  | isFalse h => h2 h

theorem em (p : Prop) [Decidable p] : p ∨ ¬p :=
  byCases Or.inl Or.inr

set_option linter.unusedVariables.funArgs false in
theorem byContradiction [dec : Decidable p] (h : ¬p → False) : p :=
  byCases id (fun np => False.elim (h np))

theorem of_not_not [Decidable p] : ¬ ¬ p → p :=
  fun hnn => byContradiction (fun hn => absurd hn hnn)

theorem not_and_iff_or_not {p q : Prop} [d₁ : Decidable p] [d₂ : Decidable q] : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q :=
  Iff.intro
    (fun h => match d₁, d₂ with
      | isTrue h₁,  isTrue h₂   => absurd (And.intro h₁ h₂) h
      | _,           isFalse h₂ => Or.inr h₂
      | isFalse h₁, _           => Or.inl h₁)
    (fun (h) ⟨hp, hq⟩ => match h with
      | Or.inl h => h hp
      | Or.inr h => h hq)

end Decidable

section
variable {p q : Prop}
/-- Transfer a decidability proof across an equivalence of propositions. -/
@[inline] def decidable_of_decidable_of_iff [Decidable p] (h : p ↔ q) : Decidable q :=
  if hp : p then
    isTrue (Iff.mp h hp)
  else
    isFalse fun hq => absurd (Iff.mpr h hq) hp

/-- Transfer a decidability proof across an equality of propositions. -/
@[inline] def decidable_of_decidable_of_eq [Decidable p] (h : p = q) : Decidable q :=
  decidable_of_decidable_of_iff (p := p) (h ▸ Iff.rfl)
end

@[macro_inline] instance {p q} [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then
    if hq : q then isTrue (fun _ => hq)
    else isFalse (fun h => absurd (h hp) hq)
  else isTrue (fun h => absurd h hp)

instance {p q} [Decidable p] [Decidable q] : Decidable (p ↔ q) :=
  if hp : p then
    if hq : q then
      isTrue ⟨fun _ => hq, fun _ => hp⟩
    else
      isFalse fun h => hq (h.1 hp)
  else
    if hq : q then
      isFalse fun h => hp (h.2 hq)
    else
      isTrue ⟨fun h => absurd h hp, fun h => absurd h hq⟩

/-! # if-then-else expression theorems -/

theorem if_pos {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem if_neg {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

/-- Split an if-then-else into cases. The `split` tactic is generally easier to use than this theorem. -/
def iteInduction {c} [inst : Decidable c] {motive : α → Sort _} {t e : α}
    (hpos : c → motive t) (hneg : ¬c → motive e) : motive (ite c t e) :=
  match inst with
  | isTrue h => hpos h
  | isFalse h => hneg h

theorem dif_pos {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬ c → α} : (dite c t e) = t hc :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem dif_neg {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬ c → α} : (dite c t e) = e hnc :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

-- Remark: dite and ite are "defally equal" when we ignore the proofs.
theorem dif_eq_if (c : Prop) {h : Decidable c} {α : Sort u} (t : α) (e : α) : dite c (fun _ => t) (fun _ => e) = ite c t e :=
  match h with
  | isTrue _    => rfl
  | isFalse _   => rfl

instance {c t e : Prop} [dC : Decidable c] [dT : Decidable t] [dE : Decidable e] : Decidable (if c then t else e) :=
  match dC with
  | isTrue _   => dT
  | isFalse _  => dE

instance {c : Prop} {t : c → Prop} {e : ¬c → Prop} [dC : Decidable c] [dT : ∀ h, Decidable (t h)] [dE : ∀ h, Decidable (e h)] : Decidable (if h : c then t h else e h) :=
  match dC with
  | isTrue hc  => dT hc
  | isFalse hc => dE hc

/-- Auxiliary definition for generating compact `noConfusion` for enumeration types -/
abbrev noConfusionTypeEnum {α : Sort u} {β : Sort v} [inst : DecidableEq β] (f : α → β) (P : Sort w) (x y : α) : Sort w :=
  (inst (f x) (f y)).casesOn
    (fun _ => P)
    (fun _ => P → P)

/-- Auxiliary definition for generating compact `noConfusion` for enumeration types -/
abbrev noConfusionEnum {α : Sort u} {β : Sort v} [inst : DecidableEq β] (f : α → β) {P : Sort w} {x y : α} (h : x = y) : noConfusionTypeEnum f P x y :=
  Decidable.casesOn
    (motive := fun (inst : Decidable (f x = f y)) => Decidable.casesOn (motive := fun _ => Sort w) inst (fun _ => P) (fun _ => P → P))
    (inst (f x) (f y))
    (fun h' => False.elim (h' (congrArg f h)))
    (fun _ => fun x => x)

/-! # Inhabited -/

instance : Inhabited Prop where
  default := True

deriving instance Inhabited for NonScalar, PNonScalar, True

/-! # Subsingleton -/

/--
A _subsingleton_ is a type with at most one element. It is either empty or has a unique element.

All propositions are subsingletons because of proof irrelevance: false propositions are empty, and
all proofs of a true proposition are equal to one another. Some non-propositional types are also
subsingletons.
-/
class Subsingleton (α : Sort u) : Prop where
  /-- Prove that `α` is a subsingleton by showing that any two elements are equal. -/
  intro ::
  /-- Any two elements of a subsingleton are equal. -/
  allEq : (a b : α) → a = b

/--
If a type is a subsingleton, then all of its elements are equal.
-/
protected theorem Subsingleton.elim {α : Sort u} [h : Subsingleton α] : (a b : α) → a = b :=
  h.allEq

/--
If two types are equal and one of them is a subsingleton, then all of their elements are
[heterogeneously equal](lean-manual://section/HEq).
-/
protected theorem Subsingleton.helim {α β : Sort u} [h₁ : Subsingleton α] (h₂ : α = β) (a : α) (b : β) : a ≍ b := by
  subst h₂
  apply heq_of_eq
  apply Subsingleton.elim

instance (p : Prop) : Subsingleton p := ⟨fun a b => proof_irrel a b⟩

instance : Subsingleton Empty  := ⟨(·.elim)⟩
instance : Subsingleton PEmpty := ⟨(·.elim)⟩

instance [Subsingleton α] [Subsingleton β] : Subsingleton (α × β) :=
  ⟨fun {..} {..} => by congr <;> apply Subsingleton.elim⟩

instance (p : Prop) : Subsingleton (Decidable p) :=
  Subsingleton.intro fun
    | isTrue t₁ => fun
      | isTrue _   => rfl
      | isFalse f₂ => absurd t₁ f₂
    | isFalse f₁ => fun
      | isTrue t₂  => absurd t₂ f₁
      | isFalse _  => rfl

example [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by congr; exact Subsingleton.elim x y⟩

theorem recSubsingleton
     {p : Prop} [h : Decidable p]
     {h₁ : p → Sort u}
     {h₂ : ¬p → Sort u}
     [h₃ : ∀ (h : p), Subsingleton (h₁ h)]
     [h₄ : ∀ (h : ¬p), Subsingleton (h₂ h)]
     : Subsingleton (h.casesOn h₂ h₁) :=
  match h with
  | isTrue h  => h₃ h
  | isFalse h => h₄ h

/--
An equivalence relation `r : α → α → Prop` is a relation that is

* reflexive: `r x x`,
* symmetric: `r x y` implies `r y x`, and
* transitive: `r x y` and `r y z` implies `r x z`.

Equality is an equivalence relation, and equivalence relations share many of the properties of
equality.
-/
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  /-- An equivalence relation is reflexive: `r x x` -/
  refl  : ∀ x, r x x
  /-- An equivalence relation is symmetric: `r x y` implies `r y x` -/
  symm  : ∀ {x y}, r x y → r y x
  /-- An equivalence relation is transitive: `r x y` and `r y z` implies `r x z` -/
  trans : ∀ {x y z}, r x y → r y z → r x z

/-- The empty relation is the relation on `α` which is always `False`. -/
def emptyRelation {α : Sort u} (_ _ : α) : Prop :=
  False

/--
`Subrelation q r` means that `q ⊆ r` or `∀ x y, q x y → r x y`.
It is the analogue of the subset relation on relations.
-/
def Subrelation {α : Sort u} (q r : α → α → Prop) :=
  ∀ {x y}, q x y → r x y

/--
The inverse image of `r : β → β → Prop` by a function `α → β` is the relation
`s : α → α → Prop` defined by `s a b = r (f a) (f b)`.
-/
def InvImage {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) : α → α → Prop :=
  fun a₁ a₂ => r (f a₁) (f a₂)

/--
The transitive closure `TransGen r` of a relation `r` is the smallest relation which is
transitive and contains `r`. `TransGen r a z` if and only if there exists a sequence
`a r b r ... r z` of length at least 1 connecting `a` to `z`.
-/
inductive Relation.TransGen {α : Sort u} (r : α → α → Prop) : α → α → Prop
  /-- If `r a b`, then `TransGen r a b`. This is the base case of the transitive closure. -/
  | single {a b} : r a b → TransGen r a b
  /-- If `TransGen r a b` and `r b c`, then `TransGen r a c`.
  This is the inductive case of the transitive closure. -/
  | tail {a b c} : TransGen r a b → r b c → TransGen r a c

/-- The transitive closure is transitive. -/
theorem Relation.TransGen.trans {α : Sort u} {r : α → α → Prop} {a b c} :
    TransGen r a b → TransGen r b c → TransGen r a c := by
  intro hab hbc
  induction hbc with
  | single h => exact TransGen.tail hab h
  | tail _ h ih => exact TransGen.tail ih h

/-! # Subtype -/

namespace Subtype

theorem exists_of_subtype {α : Type u} {p : α → Prop} : { x // p x } → Exists (fun x => p x)
  | ⟨a, h⟩ => ⟨a, h⟩

set_option linter.missingDocs false in
@[deprecated exists_of_subtype (since := "2025-04-04")]
abbrev existsOfSubtype := @exists_of_subtype

variable {α : Type u} {p : α → Prop}

protected theorem eq : ∀ {a1 a2 : {x // p x}}, val a1 = val a2 → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem eta (a : {x // p x}) (h : p (val a)) : mk (val a) h = a := by
  cases a
  exact rfl

instance {α : Type u} {p : α → Prop} [BEq α] : BEq {x : α // p x} :=
  ⟨fun x y => x.1 == y.1⟩

instance {α : Type u} {p : α → Prop} [BEq α] [ReflBEq α] : ReflBEq {x : α // p x} where
  rfl {x} := BEq.refl x.1

instance {α : Type u} {p : α → Prop} [BEq α] [LawfulBEq α] : LawfulBEq {x : α // p x} where
  eq_of_beq h := Subtype.eq (eq_of_beq h)

instance {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq {x : α // p x} :=
  fun ⟨a, h₁⟩ ⟨b, h₂⟩ =>
    if h : a = b then isTrue (by subst h; exact rfl)
    else isFalse (fun h' => Subtype.noConfusion h' (fun h' => absurd h' h))

end Subtype

/-! # Sum -/

section
variable {α : Type u} {β : Type v}

@[reducible, inherit_doc PSum.inhabitedLeft]
def Sum.inhabitedLeft [Inhabited α] : Inhabited (Sum α β) where
  default := Sum.inl default

@[reducible, inherit_doc PSum.inhabitedRight]
def Sum.inhabitedRight [Inhabited β] : Inhabited (Sum α β) where
  default := Sum.inr default

instance Sum.nonemptyLeft [h : Nonempty α] : Nonempty (Sum α β) :=
  Nonempty.elim h (fun a => ⟨Sum.inl a⟩)

instance Sum.nonemptyRight [h : Nonempty β] : Nonempty (Sum α β) :=
  Nonempty.elim h (fun b => ⟨Sum.inr b⟩)

deriving instance DecidableEq for Sum

end

/-! # Product -/

instance [h1 : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  Nonempty.elim h1 fun x =>
    Nonempty.elim h2 fun y =>
      ⟨(x, y)⟩

instance [h1 : Nonempty α] [h2 : Nonempty β] : Nonempty (MProd α β) :=
  Nonempty.elim h1 fun x =>
    Nonempty.elim h2 fun y =>
      ⟨⟨x, y⟩⟩

instance [h1 : Nonempty α] [h2 : Nonempty β] : Nonempty (PProd α β) :=
  Nonempty.elim h1 fun x =>
    Nonempty.elim h2 fun y =>
      ⟨⟨x, y⟩⟩

instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

instance [Inhabited α] [Inhabited β] : Inhabited (MProd α β) where
  default := ⟨default, default⟩

instance [Inhabited α] [Inhabited β] : Inhabited (PProd α β) where
  default := ⟨default, default⟩

instance [DecidableEq α] [DecidableEq β] : DecidableEq (α × β) :=
  fun (a, b) (a', b') =>
    match decEq a a' with
    | isTrue e₁ =>
      match decEq b b' with
      | isTrue e₂  => isTrue (e₁ ▸ e₂ ▸ rfl)
      | isFalse n₂ => isFalse fun h => Prod.noConfusion h fun _   e₂' => absurd e₂' n₂
    | isFalse n₁ => isFalse fun h => Prod.noConfusion h fun e₁' _   => absurd e₁' n₁

instance [BEq α] [BEq β] : BEq (α × β) where
  beq := fun (a₁, b₁) (a₂, b₂) => a₁ == a₂ && b₁ == b₂

/--
Lexicographical order for products.

Two pairs are lexicographically ordered if their first elements are ordered or if their first
elements are equal and their second elements are ordered.
-/
def Prod.lexLt [LT α] [LT β] (s : α × β) (t : α × β) : Prop :=
  s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)

instance Prod.lexLtDec
    [LT α] [LT β] [DecidableEq α]
    [(a b : α) → Decidable (a < b)] [(a b : β) → Decidable (a < b)]
    : (s t : α × β) → Decidable (Prod.lexLt s t) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem Prod.lexLt_def [LT α] [LT β] (s t : α × β) : (Prod.lexLt s t) = (s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)) :=
  rfl

theorem Prod.eta (p : α × β) : (p.1, p.2) = p := rfl

/--
Transforms a pair by applying functions to both elements.

Examples:
 * `(1, 2).map (· + 1) (· * 3) = (2, 6)`
 * `(1, 2).map toString (· * 3) = ("1", 6)`
-/
def Prod.map {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
    (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂
  | (a, b) => (f a, g b)

@[simp] theorem Prod.map_apply (f : α → β) (g : γ → δ) (x) (y) :
    Prod.map f g (x, y) = (f x, g y) := rfl
@[simp] theorem Prod.map_fst (f : α → β) (g : γ → δ) (x) : (Prod.map f g x).1 = f x.1 := rfl
@[simp] theorem Prod.map_snd (f : α → β) (g : γ → δ) (x) : (Prod.map f g x).2 = g x.2 := rfl

/-! # Dependent products -/

theorem Exists.of_psigma_prop {α : Sort u} {p : α → Prop} : (PSigma (fun x => p x)) → Exists (fun x => p x)
  | ⟨x, hx⟩ => ⟨x, hx⟩

protected theorem PSigma.eta {α : Sort u} {β : α → Sort v} {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
    (h₁ : a₁ = a₂) (h₂ : Eq.ndrec b₁ h₁ = b₂) : PSigma.mk a₁ b₁ = PSigma.mk a₂ b₂ := by
  subst h₁
  subst h₂
  exact rfl

/-! # Universe polymorphic unit -/

theorem PUnit.subsingleton (a b : PUnit) : a = b := by
  cases a; cases b; exact rfl

theorem PUnit.eq_punit (a : PUnit) : a = ⟨⟩ :=
  PUnit.subsingleton a ⟨⟩

instance : Subsingleton PUnit :=
  Subsingleton.intro PUnit.subsingleton

instance : Inhabited PUnit where
  default := ⟨⟩

instance : DecidableEq PUnit :=
  fun a b => isTrue (PUnit.subsingleton a b)

/-! # Setoid -/

/--
A setoid is a type with a distinguished equivalence relation, denoted `≈`.

The `Quotient` type constructor requires a `Setoid` instance.
-/
class Setoid (α : Sort u) where
  /-- `x ≈ y` is the distinguished equivalence relation of a setoid. -/
  r : α → α → Prop
  /-- The relation `x ≈ y` is an equivalence relation. -/
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

/-- A setoid's equivalence relation is reflexive. -/
theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

/-- A setoid's equivalence relation is symmetric. -/
theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

/-- A setoid's equivalence relation is transitive. -/
theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid


/-! # Propositional extensionality -/

/--
The [axiom](lean-manual://section/axioms) of **propositional extensionality**. It asserts that if
propositions `a` and `b` are logically equivalent (that is, if `a` can be proved from `b` and vice
versa), then `a` and `b` are *equal*, meaning `a` can be replaced with `b` in all contexts.

The standard logical connectives provably respect propositional extensionality. However, an axiom is
needed for higher order expressions like `P a` where `P : Prop → Prop` is unknown, as well as for
equality. Propositional extensionality is intuitionistically valid.
-/
axiom propext {a b : Prop} : (a ↔ b) → a = b

theorem Eq.propIntro {a b : Prop} (h₁ : a → b) (h₂ : b → a) : a = b :=
  propext <| Iff.intro h₁ h₂

-- Eq for Prop is now decidable if the equivalent Iff is decidable
instance {p q : Prop} [d : Decidable (p ↔ q)] : Decidable (p = q) :=
  match d with
  | isTrue h => isTrue (propext h)
  | isFalse h => isFalse fun heq => h (heq ▸ Iff.rfl)

gen_injective_theorems% Array
gen_injective_theorems% BitVec
gen_injective_theorems% Char
gen_injective_theorems% DoResultBC
gen_injective_theorems% DoResultPR
gen_injective_theorems% DoResultPRBC
gen_injective_theorems% DoResultSBC
gen_injective_theorems% EStateM.Result
gen_injective_theorems% Except
gen_injective_theorems% Fin
gen_injective_theorems% ForInStep
gen_injective_theorems% Lean.Name
gen_injective_theorems% Lean.Syntax
gen_injective_theorems% List
gen_injective_theorems% MProd
gen_injective_theorems% NonScalar
gen_injective_theorems% Option
gen_injective_theorems% PLift
gen_injective_theorems% PULift
gen_injective_theorems% PNonScalar
gen_injective_theorems% PProd
gen_injective_theorems% Prod
gen_injective_theorems% PSigma
gen_injective_theorems% PSum
gen_injective_theorems% Sigma
gen_injective_theorems% String
gen_injective_theorems% String.Pos
gen_injective_theorems% Substring
gen_injective_theorems% Subtype
gen_injective_theorems% Sum
gen_injective_theorems% Task
gen_injective_theorems% Thunk
gen_injective_theorems% UInt16
gen_injective_theorems% UInt32
gen_injective_theorems% UInt64
gen_injective_theorems% UInt8
gen_injective_theorems% ULift
gen_injective_theorems% USize

theorem Nat.succ.inj {m n : Nat} : m.succ = n.succ → m = n :=
  fun x => Nat.noConfusion x id

theorem Nat.succ.injEq (u v : Nat) : (u.succ = v.succ) = (u = v) :=
  Eq.propIntro Nat.succ.inj (congrArg Nat.succ)

@[simp] theorem beq_iff_eq [BEq α] [LawfulBEq α] {a b : α} : a == b ↔ a = b :=
  ⟨eq_of_beq, beq_of_eq⟩

/-! # Prop lemmas -/

/-- *Ex falso* for negation: from `¬a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `Not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

/-- Non-dependent eliminator for `And`. -/
abbrev And.elim (f : a → b → α) (h : a ∧ b) : α := f h.left h.right

/-- Non-dependent eliminator for `Iff`. -/
def Iff.elim (f : (a → b) → (b → a) → α) (h : a ↔ b) : α := f h.mp h.mpr

/-- Iff can now be used to do substitutions in a calculation -/
theorem Iff.subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
  Eq.subst (propext h₁) h₂

theorem Not.intro {a : Prop} (h : a → False) : ¬a := h

theorem Not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b := ⟨mt h.2, mt h.1⟩

theorem not_not_not : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := Iff.intro (fun _ => hb) (fun _ => ha)
theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b := Iff.intro ha.elim hb.elim

theorem iff_true_left  (ha : a) : (a ↔ b) ↔ b := Iff.intro (·.mp ha) (iff_of_true ha)
theorem iff_true_right (ha : a) : (b ↔ a) ↔ b := Iff.comm.trans (iff_true_left ha)

theorem iff_false_left  (ha : ¬a) : (a ↔ b) ↔ ¬b := Iff.intro (mt ·.mpr ha) (iff_of_false ha)
theorem iff_false_right (ha : ¬a) : (b ↔ a) ↔ ¬b := Iff.comm.trans (iff_false_left ha)

theorem of_iff_true    (h : a ↔ True) : a := h.mpr trivial
theorem iff_true_intro (h : a) : a ↔ True := iff_of_true h trivial

theorem eq_iff_true_of_subsingleton [Subsingleton α] (x y : α) : x = y ↔ True :=
  iff_true_intro (Subsingleton.elim ..)

theorem not_of_iff_false : (p ↔ False) → ¬p := Iff.mp
theorem iff_false_intro (h : ¬a) : a ↔ False := iff_of_false h id

theorem not_iff_false_intro (h : a) : ¬a ↔ False := iff_false_intro (not_not_intro h)
theorem not_true : (¬True) ↔ False := iff_false_intro (not_not_intro trivial)

theorem not_false_iff : (¬False) ↔ True := iff_true_intro not_false

theorem Eq.to_iff : a = b → (a ↔ b) := Iff.of_eq
theorem iff_of_eq : a = b → (a ↔ b) := Iff.of_eq
theorem neq_of_not_iff : ¬(a ↔ b) → a ≠ b := mt Iff.of_eq

theorem iff_iff_eq : (a ↔ b) ↔ a = b := Iff.intro propext Iff.of_eq
@[simp] theorem eq_iff_iff : (a = b) ↔ (a ↔ b) := iff_iff_eq.symm

theorem eq_self_iff_true (a : α)  : a = a ↔ True  := iff_true_intro rfl
theorem ne_self_iff_false (a : α) : a ≠ a ↔ False := not_iff_false_intro rfl

theorem false_of_true_iff_false (h : True ↔ False) : False := h.mp trivial
theorem false_of_true_eq_false  (h : True = False) : False := false_of_true_iff_false (Iff.of_eq h)

theorem true_eq_false_of_false : False → (True = False) := False.elim

theorem iff_def  : (a ↔ b) ↔ (a → b) ∧ (b → a) := iff_iff_implies_and_implies
theorem iff_def' : (a ↔ b) ↔ (b → a) ∧ (a → b) := Iff.trans iff_def And.comm

theorem true_iff_false : (True ↔ False) ↔ False := iff_false_intro (·.mp  True.intro)
theorem false_iff_true : (False ↔ True) ↔ False := iff_false_intro (·.mpr True.intro)

theorem iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)
theorem heq_self_iff_true (a : α) : a ≍ a ↔ True := iff_true_intro HEq.rfl

/-! ## implies -/

theorem not_not_of_not_imp : ¬(a → b) → ¬¬a := mt Not.elim

theorem not_of_not_imp {a : Prop} : ¬(a → b) → ¬b := mt fun h _ => h

@[simp] theorem imp_not_self : (a → ¬a) ↔ ¬a := Iff.intro (fun h ha => h ha ha) (fun h _ => h)

theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

theorem imp_imp_imp {a b c d : Prop} (h₀ : c → a) (h₁ : b → d) : (a → b) → (c → d) := (h₁ ∘ · ∘ h₀)

theorem imp_iff_right {a : Prop} (ha : a) : (a → b) ↔ b := Iff.intro (· ha) (fun a _ => a)

-- This is not marked `@[simp]` because we have `implies_true : (α → True) = True`
theorem imp_true_iff (α : Sort u) : (α → True) ↔ True := iff_true_intro (fun _ => trivial)

theorem false_imp_iff (a : Prop) : (False → a) ↔ True := iff_true_intro False.elim

theorem true_imp_iff {α : Prop} : (True → α) ↔ α := imp_iff_right True.intro

@[simp high] theorem imp_self : (a → a) ↔ True := iff_true_intro id

@[simp] theorem imp_false : (a → False) ↔ ¬a := Iff.rfl

theorem imp.swap : (a → b → c) ↔ (b → a → c) := Iff.intro flip flip

theorem imp_not_comm : (a → ¬b) ↔ (b → ¬a) := imp.swap

theorem imp_congr_left (h : a ↔ b) : (a → c) ↔ (b → c) := Iff.intro (· ∘ h.mpr) (· ∘ h.mp)

theorem imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
  Iff.intro (fun hab ha => (h ha).mp (hab ha)) (fun hcd ha => (h ha).mpr (hcd ha))

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
  Iff.trans (imp_congr_left h₁) (imp_congr_right h₂)

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) := imp_congr_ctx h₁ fun _ => h₂

theorem imp_iff_not (hb : ¬b) : a → b ↔ ¬a := imp_congr_right fun _ => iff_false_intro hb

/-! # Quotients -/

namespace Quot
/--
The **quotient axiom**, which asserts the equality of elements related by the quotient's relation.

The relation `r` does not need to be an equivalence relation to use this axiom. When `r` is not an
equivalence relation, the quotient is with respect to the equivalence relation generated by `r`.

`Quot.sound` is part of the built-in primitive quotient type:
 * `Quot` is the built-in quotient type.
 * `Quot.mk` places elements of the underlying type `α` into the quotient.
 * `Quot.lift` allows the definition of functions from the quotient to some other type.
 * `Quot.ind` is used to write proofs about quotients by assuming that all elements are constructed
   with `Quot.mk`; it is analogous to the [recursor](lean-manual://section/recursors) for a
   structure.

[Quotient types](lean-manual://section/quotients) are described in more detail in the Lean Language
Reference.
-/
axiom sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b

protected theorem liftBeta {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β)
    (c : (a b : α) → r a b → f a = f b)
    (a : α)
    : lift f c (Quot.mk r a) = f a :=
  rfl

protected theorem indBeta {α : Sort u} {r : α → α → Prop} {motive : Quot r → Prop}
    (p : (a : α) → motive (Quot.mk r a))
    (a : α)
    : (ind p (Quot.mk r a) : motive (Quot.mk r a)) = p a :=
  rfl

/--
Lifts a function from an underlying type to a function on a quotient, requiring that it respects the
quotient's relation.

Given a relation `r : α → α → Prop` and a quotient's value `q : Quot r`, applying a `f : α → β`
requires a proof `c` that `f` respects `r`. In this case, `Quot.liftOn q f h : β` evaluates
to the result of applying `f` to the underlying value in `α` from `q`.

`Quot.liftOn` is a version of the built-in primitive `Quot.lift` with its parameters re-ordered.

[Quotient types](lean-manual://section/quotients) are described in more detail in the Lean Language
Reference.
-/
protected abbrev liftOn {α : Sort u} {β : Sort v} {r : α → α → Prop}
  (q : Quot r) (f : α → β) (c : (a b : α) → r a b → f a = f b) : β :=
  lift f c q

@[elab_as_elim]
protected theorem inductionOn {α : Sort u} {r : α → α → Prop} {motive : Quot r → Prop}
    (q : Quot r)
    (h : (a : α) → motive (Quot.mk r a))
    : motive q :=
  ind h q

theorem exists_rep {α : Sort u} {r : α → α → Prop} (q : Quot r) : Exists (fun a => (Quot.mk r a) = q) :=
  q.inductionOn (fun a => ⟨a, rfl⟩)

section
variable {α : Sort u}
variable {r : α → α → Prop}
variable {motive : Quot r → Sort v}

/-- Auxiliary definition for `Quot.rec`. -/
@[reducible, macro_inline]
protected def indep (f : (a : α) → motive (Quot.mk r a)) (a : α) : PSigma motive :=
  ⟨Quot.mk r a, f a⟩

protected theorem indepCoherent
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    : (a b : α) → r a b → Quot.indep f a = Quot.indep f b  :=
  fun a b e => PSigma.eta (sound e) (h a b e)

protected theorem liftIndepPr1
    (f : (a : α) → motive (Quot.mk r a))
    (h : ∀ (a b : α) (p : r a b), Eq.ndrec (f a) (sound p) = f b)
    (q : Quot r)
    : (lift (Quot.indep f) (Quot.indepCoherent f h) q).1 = q := by
 induction q using Quot.ind
 exact rfl

/--
A dependent recursion principle for `Quot`. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:
 * `Quot.lift` is useful for defining non-dependent functions.
 * `Quot.ind` is useful for proving theorems about quotients.
 * `Quot.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quot.hrecOn` uses [heterogeneous equality](lean-manual://section/HEq) instead of rewriting with
   `Quot.sound`.

`Quot.recOn` is a version of this recursor that takes the quotient parameter first.
-/
@[elab_as_elim] protected abbrev rec
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    (q : Quot r) : motive q :=
  Eq.ndrecOn (Quot.liftIndepPr1 f h q) ((lift (Quot.indep f) (Quot.indepCoherent f h) q).2)

/--
A dependent recursion principle for `Quot` that takes the quotient first. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:
 * `Quot.lift` is useful for defining non-dependent functions.
 * `Quot.ind` is useful for proving theorems about quotients.
 * `Quot.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quot.hrecOn` uses [heterogeneous equality](lean-manual://section/HEq) instead of rewriting with
   `Quot.sound`.

`Quot.rec` is a version of this recursor that takes the quotient parameter last.
-/
@[elab_as_elim] protected abbrev recOn
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    : motive q :=
 q.rec f h

/--
An alternative induction principle for quotients that can be used when the target type is a
subsingleton, in which all elements are equal.

In these cases, the proof that the function respects the quotient's relation is trivial, so any
function can be lifted.

`Quot.rec` does not assume that the type is a subsingleton.
-/
@[elab_as_elim] protected abbrev recOnSubsingleton
    [h : (a : α) → Subsingleton (motive (Quot.mk r a))]
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    : motive q := by
  induction q using Quot.rec
  apply f
  apply Subsingleton.elim

/--
A dependent recursion principle for `Quot` that uses [heterogeneous
equality](lean-manual://section/HEq), analogous to a [recursor](lean-manual://section/recursors) for
a structure.

`Quot.recOn` is a version of this recursor that uses `Eq` instead of `HEq`.
-/
protected abbrev hrecOn
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (c : (a b : α) → (p : r a b) → f a ≍ f b)
    : motive q :=
  Quot.recOn q f fun a b p => eq_of_heq (eqRec_heq_iff.mpr (c a b p))

end
end Quot

set_option linter.unusedVariables.funArgs false in
/--
Quotient types coarsen the propositional equality for a type so that terms related by some
equivalence relation are considered equal. The equivalence relation is given by an instance of
`Setoid`.

Set-theoretically, `Quotient s` can seen as the set of equivalence classes of `α` modulo the
`Setoid` instance's relation `s.r`. Functions from `Quotient s` must prove that they respect `s.r`:
to define a function `f : Quotient s → β`, it is necessary to provide `f' : α → β` and prove that
for all `x : α` and `y : α`, `s.r x y → f' x = f' y`. `Quotient.lift` implements this operation.

The key quotient operators are:
 * `Quotient.mk` places elements of the underlying type `α` into the quotient.
 * `Quotient.lift` allows the definition of functions from the quotient to some other type.
 * `Quotient.sound` asserts the equality of elements related by `r`
 * `Quotient.ind` is used to write proofs about quotients by assuming that all elements are
   constructed with `Quotient.mk`.

`Quotient` is built on top of the primitive quotient type `Quot`, which does not require a proof
that the relation is an equivalence relation. `Quotient` should be used instead of `Quot` for
relations that actually are equivalence relations.
-/
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r

namespace Quotient

/--
Places an element of a type into the quotient that equates terms according to an equivalence
relation.

The setoid instance is provided explicitly. `Quotient.mk'` uses instance synthesis instead.

Given `v : α`, `Quotient.mk s v : Quotient s` is like `v`, except all observations of `v`'s value
must respect `s.r`. `Quotient.lift` allows values in a quotient to be mapped to other types, so long
as the mapping respects `s.r`.
-/
@[inline]
protected def mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s :=
  Quot.mk Setoid.r a

/--
Places an element of a type into the quotient that equates terms according to an equivalence
relation.

The equivalence relation is found by synthesizing a `Setoid` instance. `Quotient.mk` instead expects
the instance to be provided explicitly.

Given `v : α`, `Quotient.mk' v : Quotient s` is like `v`, except all observations of `v`'s value
must respect `s.r`. `Quotient.lift` allows values in a quotient to be mapped to other types, so long
as the mapping respects `s.r`.

-/
protected def mk' {α : Sort u} [s : Setoid α] (a : α) : Quotient s :=
  Quotient.mk s a

/--
The **quotient axiom**, which asserts the equality of elements related in the setoid.

Because `Quotient` is built on a lower-level type `Quot`, `Quotient.sound` is implemented as a
theorem. It is derived from `Quot.sound`, the soundness axiom for the lower-level quotient type
`Quot`.
-/
theorem sound {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b :=
  Quot.sound

/--
Lifts a function from an underlying type to a function on a quotient, requiring that it respects the
quotient's equivalence relation.

Given `s : Setoid α` and a quotient `Quotient s`, applying a function `f : α → β` requires a proof
`h` that `f` respects the equivalence relation `s.r`. In this case, the function
`Quotient.lift f h : Quotient s → β` computes the same values as `f`.

`Quotient.liftOn` is a version of this operation that takes the quotient value as its first explicit
parameter.
-/
protected abbrev lift {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) : ((a b : α) → a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`.
-/
protected theorem ind {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop} : ((a : α) → motive (Quotient.mk s a)) → (q : Quotient s) → motive q :=
  Quot.ind

/--
Lifts a function from an underlying type to a function on a quotient, requiring that it respects the
quotient's equivalence relation.

Given `s : Setoid α` and a quotient value `q : Quotient s`, applying a function `f : α → β` requires
a proof `c` that `f` respects the equivalence relation `s.r`. In this case, the term
`Quotient.liftOn q f h : β` reduces to the result of applying `f` to the underlying `α` value.

`Quotient.lift` is a version of this operation that takes the quotient value last, rather than
first.
-/
protected abbrev liftOn {α : Sort u} {β : Sort v} {s : Setoid α} (q : Quotient s) (f : α → β) (c : (a b : α) → a ≈ b → f a = f b) : β :=
  Quot.liftOn q f c

/-- The analogue of `Quot.inductionOn`: every element of `Quotient s` is of the form `Quotient.mk s a`. -/
@[elab_as_elim]
protected theorem inductionOn {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
    (q : Quotient s)
    (h : (a : α) → motive (Quotient.mk s a))
    : motive q :=
  Quot.inductionOn q h

theorem exists_rep {α : Sort u} {s : Setoid α} (q : Quotient s) : Exists (fun (a : α) => Quotient.mk s a = q) :=
  Quot.exists_rep q

section
variable {α : Sort u}
variable {s : Setoid α}
variable {motive : Quotient s → Sort v}

/--
A dependent recursion principle for `Quotient`. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:

 * `Quotient.lift` is useful for defining non-dependent functions.
 * `Quotient.ind` is useful for proving theorems about quotients.
 * `Quotient.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quotient.hrecOn` uses heterogeneous equality instead of rewriting with `Quotient.sound`.

`Quotient.recOn` is a version of this recursor that takes the quotient parameter first.
-/
@[inline, elab_as_elim]
protected def rec
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    (q : Quotient s)
    : motive q :=
  Quot.rec f h q

/--
A dependent recursion principle for `Quotient`. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:

 * `Quotient.lift` is useful for defining non-dependent functions.
 * `Quotient.ind` is useful for proving theorems about quotients.
 * `Quotient.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quotient.hrecOn` uses heterogeneous equality instead of rewriting with `Quotient.sound`.

`Quotient.rec` is a version of this recursor that takes the quotient parameter last.
-/
@[elab_as_elim]
protected abbrev recOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    : motive q :=
  Quot.recOn q f h

/--
An alternative recursion or induction principle for quotients that can be used when the target type
is a subsingleton, in which all elements are equal.

In these cases, the proof that the function respects the quotient's equivalence relation is trivial,
so any function can be lifted.

`Quotient.rec` does not assume that the target type is a subsingleton.
-/
@[elab_as_elim]
protected abbrev recOnSubsingleton
    [h : (a : α) → Subsingleton (motive (Quotient.mk s a))]
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    : motive q :=
  Quot.recOnSubsingleton (h := h) q f

/--
A dependent recursion principle for `Quotient` that uses [heterogeneous
equality](lean-manual://section/HEq), analogous to a [recursor](lean-manual://section/recursors) for
a structure.

`Quotient.recOn` is a version of this recursor that uses `Eq` instead of `HEq`.
-/
@[elab_as_elim]
protected abbrev hrecOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (c : (a b : α) → (p : a ≈ b) → f a ≍ f b)
    : motive q :=
  Quot.hrecOn q f c
end

section
universe uA uB uC
variable {α : Sort uA} {β : Sort uB} {φ : Sort uC}
variable {s₁ : Setoid α} {s₂ : Setoid β}

/--
Lifts a binary function from the underlying types to a binary function on quotients. The function
must respect both quotients' equivalence relations.

`Quotient.lift` is a version of this operation for unary functions. `Quotient.liftOn₂` is a version
that take the quotient parameters first.
-/
protected abbrev lift₂
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    : φ := by
  apply Quotient.lift (fun (a₁ : α) => Quotient.lift (f a₁) (fun (a b : β) => c a₁ a a₁ b (Setoid.refl a₁)) q₂) _ q₁
  intros
  induction q₂ using Quotient.ind
  apply c; assumption; apply Setoid.refl

/--
Lifts a binary function from the underlying types to a binary function on quotients. The function
must respect both quotients' equivalence relations.

`Quotient.liftOn` is a version of this operation for unary functions. `Quotient.lift₂` is a version
that take the quotient parameters last.
-/
protected abbrev liftOn₂
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    : φ :=
  Quotient.lift₂ f c q₁ q₂

@[elab_as_elim]
protected theorem ind₂
    {motive : Quotient s₁ → Quotient s₂ → Prop}
    (h : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    : motive q₁ q₂ := by
  induction q₁ using Quotient.ind
  induction q₂ using Quotient.ind
  apply h

@[elab_as_elim]
protected theorem inductionOn₂
    {motive : Quotient s₁ → Quotient s₂ → Prop}
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (h : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    : motive q₁ q₂ := by
  induction q₁ using Quotient.ind
  induction q₂ using Quotient.ind
  apply h

@[elab_as_elim]
protected theorem inductionOn₃
    {s₃ : Setoid φ}
    {motive : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop}
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (q₃ : Quotient s₃)
    (h : (a : α) → (b : β) → (c : φ) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b) (Quotient.mk s₃ c))
    : motive q₁ q₂ q₃ := by
  induction q₁ using Quotient.ind
  induction q₂ using Quotient.ind
  induction q₃ using Quotient.ind
  apply h

end

section Exact

variable {α : Sort u}

private def rel {s : Setoid α} (q₁ q₂ : Quotient s) : Prop :=
  Quotient.liftOn₂ q₁ q₂
    (fun a₁ a₂ => a₁ ≈ a₂)
    (fun _ _ _ _ a₁b₁ a₂b₂ =>
      propext (Iff.intro
        (fun a₁a₂ => Setoid.trans (Setoid.symm a₁b₁) (Setoid.trans a₁a₂ a₂b₂))
        (fun b₁b₂ => Setoid.trans a₁b₁ (Setoid.trans b₁b₂ (Setoid.symm a₂b₂)))))

private theorem rel.refl {s : Setoid α} (q : Quotient s) : rel q q :=
  q.inductionOn Setoid.refl

private theorem rel_of_eq {s : Setoid α} {q₁ q₂ : Quotient s} : q₁ = q₂ → rel q₁ q₂ :=
  fun h => Eq.ndrecOn h (rel.refl q₁)

/--
If two values are equal in a quotient, then they are related by its equivalence relation.
-/
theorem exact {s : Setoid α} {a b : α} : Quotient.mk s a = Quotient.mk s b → a ≈ b :=
  fun h => rel_of_eq h

end Exact

section
universe uA uB uC
variable {α : Sort uA} {β : Sort uB}
variable {s₁ : Setoid α} {s₂ : Setoid β}

/--
An alternative induction or recursion operator for defining binary operations on quotients that can
be used when the target type is a subsingleton.

In these cases, the proof that the function respects the quotient's equivalence relation is trivial,
so any function can be lifted.
-/
@[elab_as_elim]
protected abbrev recOnSubsingleton₂
    {motive : Quotient s₁ → Quotient s₂ → Sort uC}
    [s : (a : α) → (b : β) → Subsingleton (motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))]
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (g : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    : motive q₁ q₂ := by
  induction q₁ using Quot.recOnSubsingleton
  induction q₂ using Quot.recOnSubsingleton
  apply g
  intro a; apply s
  induction q₂ using Quot.recOnSubsingleton
  intro a; apply s
  infer_instance

end
end Quotient

instance Quotient.decidableEq {α : Sort u} {s : Setoid α} [d : ∀ (a b : α), Decidable (a ≈ b)]
    : DecidableEq (Quotient s) :=
  fun (q₁ q₂ : Quotient s) =>
    Quotient.recOnSubsingleton₂ q₁ q₂
      fun a₁ a₂ =>
        match d a₁ a₂ with
        | isTrue h₁  => isTrue (Quotient.sound h₁)
        | isFalse h₂ => isFalse fun h => absurd (Quotient.exact h) h₂

/-! # Function extensionality -/

/--
**Function extensionality.** If two functions return equal results for all possible arguments, then
they are equal.

It is called “extensionality” because it provides a way to prove two objects equal based on the
properties of the underlying mathematical functions, rather than based on the syntax used to denote
them. Function extensionality is a theorem that can be [proved using quotient
types](lean-manual://section/quotient-funext).
-/
theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g := by
  let eqv (f g : (x : α) → β x) := ∀ x, f x = g x
  let extfunApp (f : Quot eqv) (x : α) : β x :=
    Quot.liftOn f
      (fun (f : ∀ (x : α), β x) => f x)
      (fun _ _ h => h x)
  change extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv g)
  exact congrArg extfunApp (Quot.sound h)

/--
Like `Quot.liftOn q f h` but allows `f a` to "know" that `q = Quot.mk r a`.
-/
protected abbrev Quot.pliftOn {α : Sort u} {r : α → α → Prop}
    (q : Quot r)
    (f : (a : α) → q = Quot.mk r a → β)
    (h : ∀ (a b : α) (h h'), r a b → f a h = f b h') : β :=
  q.rec (motive := fun q' => q = q' → β) f
    (fun a b p => funext fun h' =>
      (apply_eqRec (motive := fun b _ => q = b)).trans
        (@h a b (h'.trans (sound p).symm) h' p)) rfl

/--
Like `Quotient.liftOn q f h` but allows `f a` to "know" that `q = Quotient.mk s a`.
-/
protected abbrev Quotient.pliftOn {α : Sort u} {s : Setoid α}
    (q : Quotient s)
    (f : (a : α) → q = Quotient.mk s a → β)
    (h : ∀ (a b : α) (h h'), a ≈ b → f a h = f b h') : β :=
  Quot.pliftOn q f h

instance Pi.instSubsingleton {α : Sort u} {β : α → Sort v} [∀ a, Subsingleton (β a)] :
    Subsingleton (∀ a, β a) where
  allEq f g := funext fun a => Subsingleton.elim (f a) (g a)

/-! # Squash -/

theorem equivalence_true (α : Sort u) : Equivalence fun _ _ : α ↦ True :=
  ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩

/-- Always-true relation as a `Setoid`. -/
protected def Setoid.trivial (α : Sort u) : Setoid α :=
  ⟨_, equivalence_true α⟩

/--
The quotient of `α` by the universal relation. The elements of `Squash α` are those of `α`, but all
of them are equal and cannot be distinguished.

`Squash α` is a `Subsingleton`: it is empty if `α` is empty, otherwise it has just one element. It
is the “universal `Subsingleton`” mapped from `α`.

`Nonempty α` also has these properties. It is a proposition, which means that its elements (i.e.
proofs) are erased from compiled code and represented by a dummy value. `Squash α` is a `Type u`,
and its representation in compiled code is identical to that of `α`.

Consequently, `Squash.lift` may extract an `α` value into any subsingleton type `β`, while
`Nonempty.rec` can only do the same when `β` is a proposition.

We define `Squash` in terms of `Quotient` rather than just `Quot`. This means that
`Squash` can be used when a `Quotient` argument is expected, and the setoid will be
automatically inferred.
-/
def Squash (α : Sort u) := Quotient (Setoid.trivial α)

/--
Places a value into its squash type, in which it cannot be distinguished from any other.
-/
def Squash.mk {α : Sort u} (x : α) : Squash α := Quot.mk _ x

/--
A reasoning principle that allows proofs about squashed types to assume that all values are
constructed with `Squash.mk`.
-/
theorem Squash.ind {α : Sort u} {motive : Squash α → Prop} (h : ∀ (a : α), motive (Squash.mk a)) : ∀ (q : Squash α), motive q :=
  Quot.ind h

/--
Extracts a squashed value into any subsingleton type.

If `β` is a subsingleton, a function `α → β` cannot distinguish between elements of `α` and thus
automatically respects the universal relation that `Squash` quotients with.
-/
@[inline] def Squash.lift {α β} [Subsingleton β] (s : Squash α) (f : α → β) : β :=
  Quot.lift f (fun _ _ _ => Subsingleton.elim _ _) s

instance : Subsingleton (Squash α) where
  allEq a b := by
    induction a using Squash.ind
    induction b using Squash.ind
    apply Quot.sound
    trivial

namespace Lean
/-! # Kernel reduction hints -/

/--
Depends on the correctness of the Lean compiler, interpreter, and all `[implemented_by ...]` and `[extern ...]` annotations.
-/
axiom trustCompiler : True

/--
When the kernel tries to reduce a term `Lean.reduceBool c`, it will invoke the Lean interpreter to evaluate `c`.
The kernel will not use the interpreter if `c` is not a constant.
This feature is useful for performing proofs by reflection.

Remark: the Lean frontend allows terms of the from `Lean.reduceBool t` where `t` is a term not containing
free variables. The frontend automatically declares a fresh auxiliary constant `c` and replaces the term with
`Lean.reduceBool c`. The main motivation is that the code for `t` will be pre-compiled.

Warning: by using this feature, the Lean compiler and interpreter become part of your trusted code base.
This is extra 30k lines of code. More importantly, you will probably not be able to check your development using
external type checkers that do not implement this feature.
Keep in mind that if you are using Lean as programming language, you are already trusting the Lean compiler and interpreter.
So, you are mainly losing the capability of type checking your development using external checkers.

Recall that the compiler trusts the correctness of all `[implemented_by ...]` and `[extern ...]` annotations.
If an extern function is executed, then the trusted code base will also include the implementation of the associated
foreign function.
-/
opaque reduceBool (b : Bool) : Bool :=
  -- This ensures that `#print axioms` will track use of `reduceBool`.
  have := trustCompiler
  b

/--
Similar to `Lean.reduceBool` for closed `Nat` terms.

Remark: we do not have plans for supporting a generic `reduceValue {α} (a : α) : α := a`.
The main issue is that it is non-trivial to convert an arbitrary runtime object back into a Lean expression.
We believe `Lean.reduceBool` enables most interesting applications (e.g., proof by reflection).
-/
opaque reduceNat (n : Nat) : Nat :=
  -- This ensures that `#print axioms` will track use of `reduceNat`.
  have := trustCompiler
  n


/--
The axiom `ofReduceBool` is used to perform proofs by reflection. See `reduceBool`.

This axiom is usually not used directly, because it has some syntactic restrictions.
Instead, the `native_decide` tactic can be used to prove any proposition whose
decidability instance can be evaluated to `true` using the lean compiler / interpreter.

Warning: by using this feature, the Lean compiler and interpreter become part of your trusted code base.
This is extra 30k lines of code. More importantly, you will probably not be able to check your development using
external type checkers that do not implement this feature.
Keep in mind that if you are using Lean as programming language, you are already trusting the Lean compiler and interpreter.
So, you are mainly losing the capability of type checking your development using external checkers.
-/
axiom ofReduceBool (a b : Bool) (h : reduceBool a = b) : a = b

/--
The axiom `ofReduceNat` is used to perform proofs by reflection. See `reduceBool`.

Warning: by using this feature, the Lean compiler and interpreter become part of your trusted code base.
This is extra 30k lines of code. More importantly, you will probably not be able to check your development using
external type checkers that do not implement this feature.
Keep in mind that if you are using Lean as programming language, you are already trusting the Lean compiler and interpreter.
So, you are mainly losing the capability of type checking your development using external checkers.
-/
axiom ofReduceNat (a b : Nat) (h : reduceNat a = b) : a = b


/--
The term `opaqueId x` will not be reduced by the kernel.
-/
opaque opaqueId {α : Sort u} (x : α) : α := x

end Lean

@[simp] theorem ge_iff_le [LE α] {x y : α} : x ≥ y ↔ y ≤ x := Iff.rfl

@[simp] theorem gt_iff_lt [LT α] {x y : α} : x > y ↔ y < x := Iff.rfl

theorem le_of_eq_of_le {a b c : α} [LE α] (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c := h₁ ▸ h₂

theorem le_of_le_of_eq {a b c : α} [LE α] (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := h₂ ▸ h₁

theorem lt_of_eq_of_lt {a b c : α} [LT α] (h₁ : a = b) (h₂ : b < c) : a < c := h₁ ▸ h₂

theorem lt_of_lt_of_eq {a b c : α} [LT α] (h₁ : a < b) (h₂ : b = c) : a < c := h₂ ▸ h₁

namespace Std
variable {α : Sort u}

/--
`Associative op` indicates `op` is an associative operation,
i.e. `(a ∘ b) ∘ c = a ∘ (b ∘ c)`.
-/
class Associative (op : α → α → α) : Prop where
  /-- An associative operation satisfies `(a ∘ b) ∘ c = a ∘ (b ∘ c)`. -/
  assoc : (a b c : α) → op (op a b) c = op a (op b c)

/--
`Commutative op` says that `op` is a commutative operation,
i.e. `a ∘ b = b ∘ a`.
-/
class Commutative (op : α → α → α) : Prop where
  /-- A commutative operation satisfies `a ∘ b = b ∘ a`. -/
  comm : (a b : α) → op a b = op b a

/--
`IdempotentOp op` indicates `op` is an idempotent binary operation.
i.e. `a ∘ a = a`.
-/
class IdempotentOp (op : α → α → α) : Prop where
  /-- An idempotent operation satisfies `a ∘ a = a`. -/
  idempotent : (x : α) → op x x = x

/--
`LeftIdentify op o` indicates `o` is a left identity of `op`.

This class does not require a proof that `o` is an identity, and
is used primarily for inferring the identity using class resolution.
-/
class LeftIdentity (op : α → β → β) (o : outParam α) : Prop

/--
`LawfulLeftIdentify op o` indicates `o` is a verified left identity of
`op`.
-/
class LawfulLeftIdentity (op : α → β → β) (o : outParam α) : Prop extends LeftIdentity op o where
  /-- Left identity `o` is an identity. -/
  left_id : ∀ a, op o a = a

/--
`RightIdentify op o` indicates `o` is a right identity `o` of `op`.

This class does not require a proof that `o` is an identity, and is used
primarily for inferring the identity using class resolution.
-/
class RightIdentity (op : α → β → α) (o : outParam β) : Prop

/--
`LawfulRightIdentify op o` indicates `o` is a verified right identity of
`op`.
-/
class LawfulRightIdentity (op : α → β → α) (o : outParam β) : Prop extends RightIdentity op o where
  /-- Right identity `o` is an identity. -/
  right_id : ∀ a, op a o = a

/--
`Identity op o` indicates `o` is a left and right identity of `op`.

This class does not require a proof that `o` is an identity, and is used
primarily for inferring the identity using class resolution.
-/
class Identity (op : α → α → α) (o : outParam α) : Prop extends LeftIdentity op o, RightIdentity op o

/--
`LawfulIdentity op o` indicates `o` is a verified left and right
identity of `op`.
-/
class LawfulIdentity (op : α → α → α) (o : outParam α) : Prop extends Identity op o, LawfulLeftIdentity op o, LawfulRightIdentity op o

/--
`LawfulCommIdentity` can simplify defining instances of `LawfulIdentity`
on commutative functions by requiring only a left or right identity
proof.

This class is intended for simplifying defining instances of
`LawfulIdentity` and functions needed commutative operations with
identity should just add a `LawfulIdentity` constraint.
-/
class LawfulCommIdentity (op : α → α → α) (o : outParam α) [hc : Commutative op] : Prop extends LawfulIdentity op o where
  left_id a := Eq.trans (hc.comm o a) (right_id a)
  right_id a := Eq.trans (hc.comm a o) (left_id a)

instance : Commutative Or := ⟨fun _ _ => propext or_comm⟩
instance : Commutative And := ⟨fun _ _ => propext and_comm⟩
instance : Commutative Iff := ⟨fun _ _ => propext iff_comm⟩

/-- `Refl r` means the binary relation `r` is reflexive, that is, `r x x` always holds. -/
class Refl (r : α → α → Prop) : Prop where
  /-- A reflexive relation satisfies `r a a`. -/
  refl : ∀ a, r a a

/-- `Antisymm r` says that `r` is antisymmetric, that is, `r a b → r b a → a = b`. -/
class Antisymm (r : α → α → Prop) : Prop where
  /-- An antisymmetric relation `r` satisfies `r a b → r b a → a = b`. -/
  antisymm (a b : α) : r a b → r b a → a = b

/-- `Asymm r` means that the binary relation `r` is asymmetric, that is,
`r a b → ¬ r b a`. -/
class Asymm (r : α → α → Prop) : Prop where
  /-- An asymmetric relation satisfies `r a b → ¬ r b a`. -/
  asymm : ∀ a b, r a b → ¬r b a

/-- `Symm r` means that the binary relation `r` is symmetric, that is, `r a b → r b a`.  -/
class Symm (r : α → α → Prop) : Prop where
  /-- A symmetric relation satisfies `r a b → r b a`. -/
  symm : ∀ a b, r a b → r b a

/-- `Total X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`. -/
class Total (r : α → α → Prop) : Prop where
  /-- A total relation satisfies `r a b ∨ r b a`. -/
  total : ∀ a b, r a b ∨ r b a

/-- `Irrefl r` means the binary relation `r` is irreflexive, that is, `r x x` never
holds. -/
class Irrefl (r : α → α → Prop) : Prop where
  /-- An irreflexive relation satisfies `¬ r a a`. -/
  irrefl : ∀ a, ¬r a a

end Std

/-- Deprecated alias for `XorOp`. -/
@[deprecated XorOp (since := "2025-07-30")]
abbrev Xor := XorOp
