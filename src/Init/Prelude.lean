/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude -- Don't import Init, because we're in Init itself
set_option linter.missingDocs true -- keep it documented

/-!
# Init.Prelude

This is the first file in the Lean import hierarchy. It is responsible for setting
up basic definitions, most of which Lean already has "built in knowledge" about,
so it is important that they be set up in exactly this way. (For example, Lean will
use `PUnit` in the desugaring of `do` notation, or in the pattern match compiler.)

-/

universe u v w

/--
The identity function. `id` takes an implicit argument `α : Sort u`
(a type in any universe), and an argument `a : α`, and returns `a`.

Although this may look like a useless function, one application of the identity
function is to explicitly put a type on an expression. If `e` has type `T`,
and `T'` is definitionally equal to `T`, then `@id T' e` typechecks, and Lean
knows that this expression has type `T'` rather than `T`. This can make a
difference for typeclass inference, since `T` and `T'` may have different
typeclass instances on them. `show T' from e` is sugar for an `@id T' e`
expression.
-/
@[inline] def id {α : Sort u} (a : α) : α := a

/--
Function composition is the act of pipelining the result of one function, to the input of another, creating an entirely new function.
Example:
```
#eval Function.comp List.reverse (List.drop 2) [3, 2, 4, 1]
-- [1, 4]
```
You can use the notation `f ∘ g` as shorthand for `Function.comp f g`.
```
#eval (List.reverse ∘ List.drop 2) [3, 2, 4, 1]
-- [1, 4]
```
A simpler way of thinking about it, is that `List.reverse ∘ List.drop 2`
is equivalent to `fun xs => List.reverse (List.drop 2 xs)`,
the benefit is that the meaning of composition is obvious,
and the representation is compact.
-/
@[inline] def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

/--
The constant function. If `a : α`, then `Function.const β a : β → α` is the
"constant function with value `a`", that is, `Function.const β a b = a`.
```
example (b : Bool) : Function.const Bool 10 b = 10 :=
  rfl

#check Function.const Bool 10
-- Bool → Nat
```
-/
@[inline] def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun _ => a

/--
The encoding of `let_fun x := v; b` is `letFun v (fun x => b)`.
This is equal to `(fun x => b) v`, so the value of `x` is not accessible to `b`.
This is in contrast to `let x := v; b`, where the value of `x` is accessible to `b`.

There is special support for `letFun`.
Both WHNF and `simp` are aware of `letFun` and can reduce it when zeta reduction is enabled,
despite the fact it is marked `irreducible`.
For metaprogramming, the function `Lean.Expr.letFun?` can be used to recognize a `let_fun` expression
to extract its parts as if it were a `let` expression.
-/
@[irreducible] def letFun {α : Sort u} {β : α → Sort v} (v : α) (f : (x : α) → β x) : β v := f v

set_option checkBinderAnnotations false in
/--
`inferInstance` synthesizes a value of any target type by typeclass
inference. This function has the same type signature as the identity
function, but the square brackets on the `[i : α]` argument means that it will
attempt to construct this argument by typeclass inference. (This will fail if
`α` is not a `class`.) Example:
```
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

example : foo.default = (default, default) :=
  rfl
```
-/
abbrev inferInstance {α : Sort u} [i : α] : α := i

set_option checkBinderAnnotations false in
/-- `inferInstanceAs α` synthesizes a value of any target type by typeclass
inference. This is just like `inferInstance` except that `α` is given
explicitly instead of being inferred from the target type. It is especially
useful when the target type is some `α'` which is definitionally equal to `α`,
but the instance we are looking for is only registered for `α` (because
typeclass search does not unfold most definitions, but definitional equality
does.) Example:
```
#check inferInstanceAs (Inhabited Nat) -- Inhabited Nat
```
-/
abbrev inferInstanceAs (α : Sort u) [i : α] : α := i

set_option bootstrap.inductiveCheckResultingUniverse false in
/--
The unit type, the canonical type with one element, named `unit` or `()`.
This is the universe-polymorphic version of `Unit`; it is preferred to use
`Unit` instead where applicable.
For more information about universe levels: [Types as objects](https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects)
-/
inductive PUnit : Sort u where
  /-- `PUnit.unit : PUnit` is the canonical element of the unit type. -/
  | unit : PUnit

/--
The unit type, the canonical type with one element, named `unit` or `()`.
In other words, it describes only a single value, which consists of said constructor applied
to no arguments whatsoever.
The `Unit` type is similar to `void` in languages derived from C.

`Unit` is actually defined as `PUnit.{1}` where `PUnit` is the universe
polymorphic version. The `Unit` should be preferred over `PUnit` where possible to avoid
unnecessary universe parameters.

In functional programming, `Unit` is the return type of things that "return
nothing", since a type with one element conveys no additional information.
When programming with monads, the type `m Unit` represents an action that has
some side effects but does not return a value, while `m α` would be an action
that has side effects and returns a value of type `α`.
-/
abbrev Unit : Type := PUnit

/--
`Unit.unit : Unit` is the canonical element of the unit type.
It can also be written as `()`.
-/
@[match_pattern] abbrev Unit.unit : Unit := PUnit.unit

/-- Marker for information that has been erased by the code generator. -/
unsafe axiom lcErased : Type

/-- Marker for type dependency that has been erased by the code generator. -/
unsafe axiom lcAny : Type

/--
Auxiliary unsafe constant used by the Compiler when erasing proofs from code.

It may look strange to have an axiom that says "every proposition is true",
since this is obviously unsound, but the `unsafe` marker ensures that the
kernel will not let this through into regular proofs. The lower levels of the
code generator don't need proofs in terms, so this is used to stub the proofs
out.
-/
unsafe axiom lcProof {α : Prop} : α

/--
Auxiliary unsafe constant used by the Compiler when erasing casts.
-/
unsafe axiom lcCast {α : Sort u} {β : Sort v} (a : α) : β


/--
Auxiliary unsafe constant used by the Compiler to mark unreachable code.

Like `lcProof`, this is an `unsafe axiom`, which means that even though it is
not sound, the kernel will not let us use it for regular proofs.

Executing this expression to actually synthesize a value of type `α` causes
**immediate undefined behavior**, and the compiler does take advantage of this
to optimize the code assuming that it is not called. If it is not optimized out,
it is likely to appear as a print message saying "unreachable code", but this
behavior is not guaranteed or stable in any way.
-/
unsafe axiom lcUnreachable {α : Sort u} : α

/--
`True` is a proposition and has only an introduction rule, `True.intro : True`.
In other words, `True` is simply true, and has a canonical proof, `True.intro`
For more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
inductive True : Prop where
  /-- `True` is true, and `True.intro` (or more commonly, `trivial`)
  is the proof. -/
  | intro : True

/--
`False` is the empty proposition. Thus, it has no introduction rules.
It represents a contradiction. `False` elimination rule, `False.rec`,
expresses the fact that anything follows from a contradiction.
This rule is sometimes called ex falso (short for ex falso sequitur quodlibet),
or the principle of explosion.
For more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
inductive False : Prop

/--
The empty type. It has no constructors. The `Empty.rec`
eliminator expresses the fact that anything follows from the empty type.
-/
inductive Empty : Type

set_option bootstrap.inductiveCheckResultingUniverse false in
/--
The universe-polymorphic empty type. Prefer `Empty` or `False` where
possible.
-/
inductive PEmpty : Sort u where

/--
`Not p`, or `¬p`, is the negation of `p`. It is defined to be `p → False`,
so if your goal is `¬p` you can use `intro h` to turn the goal into
`h : p ⊢ False`, and if you have `hn : ¬p` and `h : p` then `hn h : False`
and `(hn h).elim` will prove anything.
For more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
def Not (a : Prop) : Prop := a → False

/--
`False.elim : False → C` says that from `False`, any desired proposition
`C` holds. Also known as ex falso quodlibet (EFQ) or the principle of explosion.

The target type is actually `C : Sort u` which means it works for both
propositions and types. When executed, this acts like an "unreachable"
instruction: it is **undefined behavior** to run, but it will probably print
"unreachable code". (You would need to construct a proof of false to run it
anyway, which you can only do using `sorry` or unsound axioms.)
-/
@[macro_inline] def False.elim {C : Sort u} (h : False) : C :=
  h.rec

/--
Anything follows from two contradictory hypotheses. Example:
```
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```
For more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
@[macro_inline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
  (h₂ h₁).rec

/--
The equality relation. It has one introduction rule, `Eq.refl`.
We use `a = b` as notation for `Eq a b`.
A fundamental property of equality is that it is an equivalence relation.
```
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```
Equality is much more than an equivalence relation, however. It has the important property that every assertion
respects the equivalence, in the sense that we can substitute equal expressions without changing the truth value.
That is, given `h1 : a = b` and `h2 : p a`, we can construct a proof for `p b` using substitution: `Eq.subst h1 h2`.
Example:
```
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```
The triangle in the second presentation is a macro built on top of `Eq.subst` and `Eq.symm`, and you can enter it by typing `\t`.
For more information: [Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
inductive Eq : α → α → Prop where
  /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
  equality type. See also `rfl`, which is usually used instead. -/
  | refl (a : α) : Eq a a

/-- Non-dependent recursor for the equality type. -/
@[simp] abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

/--
`rfl : a = a` is the unique constructor of the equality type. This is the
same as `Eq.refl` except that it takes `a` implicitly instead of explicitly.

This is a more powerful theorem than it may appear at first, because although
the statement of the theorem is `a = a`, Lean will allow anything that is
definitionally equal to that type. So, for instance, `2 + 2 = 4` is proven in
Lean by `rfl`, because both sides are the same up to definitional equality.
-/
@[match_pattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

/-- `id x = x`, as a `@[simp]` lemma. -/
@[simp] theorem id_eq (a : α) : Eq (id a) a := rfl

/--
The substitution principle for equality. If `a = b ` and `P a` holds,
then `P b` also holds. We conventionally use the name `motive` for `P` here,
so that you can specify it explicitly using e.g.
`Eq.subst (motive := fun x => x < 5)` if it is not otherwise inferred correctly.

This theorem is the underlying mechanism behind the `rw` tactic, which is
essentially a fancy algorithm for finding good `motive` arguments to usefully
apply this theorem to replace occurrences of `a` with `b` in the goal or
hypotheses.

For more information: [Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

/--
Equality is symmetric: if `a = b` then `b = a`.

Because this is in the `Eq` namespace, if you have a variable `h : a = b`,
`h.symm` can be used as shorthand for `Eq.symm h` as a proof of `b = a`.

For more information: [Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
@[symm] theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h ▸ rfl

/--
Equality is transitive: if `a = b` and `b = c` then `a = c`.

Because this is in the `Eq` namespace, if you have variables or expressions
`h₁ : a = b` and `h₂ : b = c`, you can use `h₁.trans h₂ : a = c` as shorthand
for `Eq.trans h₁ h₂`.

For more information: [Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  h₂ ▸ h₁

/--
Cast across a type equality. If `h : α = β` is an equality of types, and
`a : α`, then `a : β` will usually not typecheck directly, but this function
will allow you to work around this and embed `a` in type `β` as `cast h a : β`.

It is best to avoid this function if you can, because it is more complicated
to reason about terms containing casts, but if the types don't match up
definitionally sometimes there isn't anything better you can do.

For more information: [Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
@[macro_inline] def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec a

/--
Congruence in the function argument: if `a₁ = a₂` then `f a₁ = f a₂` for
any (nondependent) function `f`. This is more powerful than it might look at first, because
you can also use a lambda expression for `f` to prove that
`<something containing a₁> = <something containing a₂>`. This function is used
internally by tactics like `congr` and `simp` to apply equalities inside
subterms.

For more information: [Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl

/--
Congruence in both function and argument. If `f₁ = f₂` and `a₁ = a₂` then
`f₁ a₁ = f₂ a₂`. This only works for nondependent functions; the theorem
statement is more complex in the dependent case.

For more information: [Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : Eq f₁ f₂) (h₂ : Eq a₁ a₂) : Eq (f₁ a₁) (f₂ a₂) :=
  h₁ ▸ h₂ ▸ rfl

/-- Congruence in the function part of an application: If `f = g` then `f a = g a`. -/
theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : Eq f g) (a : α) : Eq (f a) (g a) :=
  h ▸ rfl

/-!
Initialize the Quotient Module, which effectively adds the following definitions:
```
opaque Quot {α : Sort u} (r : α → α → Prop) : Sort u

opaque Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : Quot r

opaque Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → Eq (f a) (f b)) → Quot r → β

opaque Quot.ind {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} :
  (∀ a : α, β (Quot.mk r a)) → ∀ q : Quot r, β q
```
-/
init_quot

/--
Let `α` be any type, and let `r` be an equivalence relation on `α`.
It is mathematically common to form the "quotient" `α / r`, that is, the type of
elements of `α` "modulo" `r`. Set theoretically, one can view `α / r` as the set
of equivalence classes of `α` modulo `r`. If `f : α → β` is any function that
respects the equivalence relation in the sense that for every `x y : α`,
`r x y` implies `f x = f y`, then f "lifts" to a function `f' : α / r → β`
defined on each equivalence class `⟦x⟧` by `f' ⟦x⟧ = f x`.
Lean extends the Calculus of Constructions with additional constants that
perform exactly these constructions, and installs this last equation as a
definitional reduction rule.

Given a type `α` and any binary relation `r` on `α`, `Quot r` is a type. Note
that `r` is not required to be an equivalence relation. `Quot` is the basic
building block used to construct later the type `Quotient`.
-/
add_decl_doc Quot

/--
Given a type `α` and any binary relation `r` on `α`, `Quot.mk` maps `α` to `Quot r`.
So that if `r : α → α → Prop` and `a : α`, then `Quot.mk r a` is an element of `Quot r`.

See `Quot`.
-/
add_decl_doc Quot.mk

/--
Given a type `α` and any binary relation `r` on `α`,
`Quot.ind` says that every element of `Quot r` is of the form `Quot.mk r a`.

See `Quot` and `Quot.lift`.
-/
add_decl_doc Quot.ind

/--
Given a type `α`, any binary relation `r` on `α`, a function `f : α → β`, and a proof `h`
that `f` respects the relation `r`, then `Quot.lift f h` is the corresponding function on `Quot r`.

The idea is that for each element `a` in `α`, the function `Quot.lift f h` maps `Quot.mk r a`
(the `r`-class containing `a`) to `f a`, wherein `h` shows that this function is well defined.
In fact, the computation principle is declared as a reduction rule.
-/
add_decl_doc Quot.lift

/--
Unsafe auxiliary constant used by the compiler to erase `Quot.lift`.
-/
unsafe axiom Quot.lcInv {α : Sort u} {r : α → α → Prop} (q : Quot r) : α

/--
Heterogeneous equality. `HEq a b` asserts that `a` and `b` have the same
type, and casting `a` across the equality yields `b`, and vice versa.

You should avoid using this type if you can. Heterogeneous equality does not
have all the same properties as `Eq`, because the assumption that the types of
`a` and `b` are equal is often too weak to prove theorems of interest. One
important non-theorem is the analogue of `congr`: If `HEq f g` and `HEq x y`
and `f x` and `g y` are well typed it does not follow that `HEq (f x) (g y)`.
(This does follow if you have `f = g` instead.) However if `a` and `b` have
the same type then `a = b` and `HEq a b` are equivalent.
-/
inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  /-- Reflexivity of heterogeneous equality. -/
  | refl (a : α) : HEq a a

/-- A version of `HEq.refl` with an implicit argument. -/
@[match_pattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a :=
  HEq.refl a

theorem eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ => rfl)
  this α α a a' h rfl

/--
Product type (aka pair). You can use `α × β` as notation for `Prod α β`.
Given `a : α` and `b : β`, `Prod.mk a b : Prod α β`. You can use `(a, b)`
as notation for `Prod.mk a b`. Moreover, `(a, b, c)` is notation for
`Prod.mk a (Prod.mk b c)`.
Given `p : Prod α β`, `p.1 : α` and `p.2 : β`. They are short for `Prod.fst p`
and `Prod.snd p` respectively. You can also write `p.fst` and `p.snd`.
For more information: [Constructors with Arguments](https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html?highlight=Prod#constructors-with-arguments)
-/
structure Prod (α : Type u) (β : Type v) where
  /-- Constructs a pair from two terms. -/
  mk ::
  /-- The first projection out of a pair. if `p : α × β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : α × β` then `p.2 : β`. -/
  snd : β

attribute [unbox] Prod

/--
Similar to `Prod`, but `α` and `β` can be propositions.
You can use `α ×' β` as notation for `PProd α β`.
We use this type internally to automatically generate the `brecOn` recursor.
-/
structure PProd (α : Sort u) (β : Sort v) where
  /-- The first projection out of a pair. if `p : PProd α β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : PProd α β` then `p.2 : β`. -/
  snd : β

/--
Similar to `Prod`, but `α` and `β` are in the same universe.
We say `MProd` is the universe monomorphic product type.
-/
structure MProd (α β : Type u) where
  /-- The first projection out of a pair. if `p : MProd α β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : MProd α β` then `p.2 : β`. -/
  snd : β

/--
`And a b`, or `a ∧ b`, is the conjunction of propositions. It can be
constructed and destructed like a pair: if `ha : a` and `hb : b` then
`⟨ha, hb⟩ : a ∧ b`, and if `h : a ∧ b` then `h.left : a` and `h.right : b`.
-/
@[pp_using_anonymous_constructor]
structure And (a b : Prop) : Prop where
  /-- `And.intro : a → b → a ∧ b` is the constructor for the And operation. -/
  intro ::
  /-- Extract the left conjunct from a conjunction. `h : a ∧ b` then
  `h.left`, also notated as `h.1`, is a proof of `a`. -/
  left : a
  /-- Extract the right conjunct from a conjunction. `h : a ∧ b` then
  `h.right`, also notated as `h.2`, is a proof of `b`. -/
  right : b

/--
`Or a b`, or `a ∨ b`, is the disjunction of propositions. There are two
constructors for `Or`, called `Or.inl : a → a ∨ b` and `Or.inr : b → a ∨ b`,
and you can use `match` or `cases` to destruct an `Or` assumption into the
two cases.
-/
inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b

/-- Alias for `Or.inl`. -/
theorem Or.intro_left (b : Prop) (h : a) : Or a b :=
  Or.inl h

/-- Alias for `Or.inr`. -/
theorem Or.intro_right (a : Prop) (h : b) : Or a b :=
  Or.inr h

/--
Proof by cases on an `Or`. If `a ∨ b`, and both `a` and `b` imply
proposition `c`, then `c` is true.
-/
theorem Or.elim {c : Prop} (h : Or a b) (left : a → c) (right : b → c) : c :=
  match h with
  | Or.inl h => left h
  | Or.inr h => right h

theorem Or.resolve_left  (h: Or a b) (na : Not a) : b := h.elim (absurd · na) id
theorem Or.resolve_right (h: Or a b) (nb : Not b) : a := h.elim id (absurd · nb)
theorem Or.neg_resolve_left  (h : Or (Not a) b) (ha : a) : b := h.elim (absurd ha) id
theorem Or.neg_resolve_right (h : Or a (Not b)) (nb : b) : a := h.elim id (absurd nb)

/--
`Bool` is the type of boolean values, `true` and `false`. Classically,
this is equivalent to `Prop` (the type of propositions), but the distinction
is important for programming, because values of type `Prop` are erased in the
code generator, while `Bool` corresponds to the type called `bool` or `boolean`
in most programming languages.
-/
inductive Bool : Type where
  /-- The boolean value `false`, not to be confused with the proposition `False`. -/
  | false : Bool
  /-- The boolean value `true`, not to be confused with the proposition `True`. -/
  | true : Bool

export Bool (false true)

/--
`Subtype p`, usually written as `{x : α // p x}`, is a type which
represents all the elements `x : α` for which `p x` is true. It is structurally
a pair-like type, so if you have `x : α` and `h : p x` then
`⟨x, h⟩ : {x // p x}`. An element `s : {x // p x}` will coerce to `α` but
you can also make it explicit using `s.1` or `s.val`.
-/
@[pp_using_anonymous_constructor]
structure Subtype {α : Sort u} (p : α → Prop) where
  /-- If `s : {x // p x}` then `s.val : α` is the underlying element in the base
  type. You can also write this as `s.1`, or simply as `s` when the type is
  known from context. -/
  val : α
  /-- If `s : {x // p x}` then `s.2` or `s.property` is the assertion that
  `p s.1`, that is, that `s` is in fact an element for which `p` holds. -/
  property : p val

set_option linter.unusedVariables.funArgs false in
/--
Gadget for optional parameter support.

A binder like `(x : α := default)` in a declaration is syntax sugar for
`x : optParam α default`, and triggers the elaborator to attempt to use
`default` to supply the argument if it is not supplied.
-/
@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

/--
Gadget for marking output parameters in type classes.

For example, the `Membership` class is defined as:
```
class Membership (α : outParam (Type u)) (γ : Type v)
```
This means that whenever a typeclass goal of the form `Membership ?α ?γ` comes
up, Lean will wait to solve it until `?γ` is known, but then it will run
typeclass inference, and take the first solution it finds, for any value of `?α`,
which thereby determines what `?α` should be.

This expresses that in a term like `a ∈ s`, `s` might be a `Set α` or
`List α` or some other type with a membership operation, and in each case
the "member" type `α` is determined by looking at the container type.
-/
@[reducible] def outParam (α : Sort u) : Sort u := α

/--
Gadget for marking semi output parameters in type classes.

Semi-output parameters influence the order in which arguments to type class
instances are processed.  Lean determines an order where all non-(semi-)output
parameters to the instance argument have to be figured out before attempting to
synthesize an argument (that is, they do not contain assignable metavariables
created during TC synthesis). This rules out instances such as `[Mul β] : Add
α` (because `β` could be anything). Marking a parameter as semi-output is a
promise that instances of the type class will always fill in a value for that
parameter.

For example, the `Coe` class is defined as:
```
class Coe (α : semiOutParam (Sort u)) (β : Sort v)
```
This means that all `Coe` instances should provide a concrete value for `α`
(i.e., not an assignable metavariable). An instance like `Coe Nat Int` or `Coe
α (Option α)` is fine, but `Coe α Nat` is not since it does not provide a value
for `α`.
-/
@[reducible] def semiOutParam (α : Sort u) : Sort u := α

set_option linter.unusedVariables.funArgs false in
/-- Auxiliary declaration used to implement named patterns like `x@h:p`. -/
@[reducible] def namedPattern {α : Sort u} (x a : α) (h : Eq x a) : α := a

/--
Auxiliary axiom used to implement the `sorry` term and tactic.

The `sorry` term/tactic expands to `sorryAx _ (synthetic := false)`.
It is intended for stubbing-out incomplete parts of a value or proof while still having a syntactically correct skeleton.
Lean will give a warning whenever a declaration uses `sorry`, so you aren't likely to miss it,
but you can check if a declaration depends on `sorry` either directly or indirectly by looking for `sorryAx` in the output
of the `#print axioms my_thm` command.

The `synthetic` flag is false when a `sorry` is written explicitly by the user, but it is
set to `true` when a tactic fails to prove a goal, or if there is a type error
in the expression. A synthetic `sorry` acts like a regular one, except that it
suppresses follow-up errors in order to prevent an error from causing a cascade
of other errors because the desired term was not constructed.
-/
@[extern "lean_sorry", never_extract]
axiom sorryAx (α : Sort u) (synthetic : Bool) : α

theorem eq_false_of_ne_true : {b : Bool} → Not (Eq b true) → Eq b false
  | true, h => False.elim (h rfl)
  | false, _ => rfl

theorem eq_true_of_ne_false : {b : Bool} → Not (Eq b false) → Eq b true
  | true, _ => rfl
  | false, h => False.elim (h rfl)

theorem ne_false_of_eq_true : {b : Bool} → Eq b true → Not (Eq b false)
  | true, _  => fun h => Bool.noConfusion h
  | false, h => Bool.noConfusion h

theorem ne_true_of_eq_false : {b : Bool} → Eq b false → Not (Eq b true)
  | true, h  => Bool.noConfusion h
  | false, _ => fun h => Bool.noConfusion h

/--
`Inhabited α` is a typeclass that says that `α` has a designated element,
called `(default : α)`. This is sometimes referred to as a "pointed type".

This class is used by functions that need to return a value of the type
when called "out of domain". For example, `Array.get! arr i : α` returns
a value of type `α` when `arr : Array α`, but if `i` is not in range of
the array, it reports a panic message, but this does not halt the program,
so it must still return a value of type `α` (and in fact this is required
for logical consistency), so in this case it returns `default`.
-/
class Inhabited (α : Sort u) where
  /-- `default` is a function that produces a "default" element of any
  `Inhabited` type. This element does not have any particular specified
  properties, but it is often an all-zeroes value. -/
  default : α

export Inhabited (default)

/--
`Nonempty α` is a typeclass that says that `α` is not an empty type,
that is, there exists an element in the type. It differs from `Inhabited α`
in that `Nonempty α` is a `Prop`, which means that it does not actually carry
an element of `α`, only a proof that *there exists* such an element.
Given `Nonempty α`, you can construct an element of `α` *nonconstructively*
using `Classical.choice`.
-/
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α

/--
**The axiom of choice**. `Nonempty α` is a proof that `α` has an element,
but the element itself is erased. The axiom `choice` supplies a particular
element of `α` given only this proof.

The textbook axiom of choice normally makes a family of choices all at once,
but that is implied from this formulation, because if `α : ι → Type` is a
family of types and `h : ∀ i, Nonempty (α i)` is a proof that they are all
nonempty, then `fun i => Classical.choice (h i) : ∀ i, α i` is a family of
chosen elements. This is actually a bit stronger than the ZFC choice axiom;
this is sometimes called "[global choice](https://en.wikipedia.org/wiki/Axiom_of_global_choice)".

In Lean, we use the axiom of choice to derive the law of excluded middle
(see `Classical.em`), so it will often show up in axiom listings where you
may not expect. You can use `#print axioms my_thm` to find out if a given
theorem depends on this or other axioms.

This axiom can be used to construct "data", but obviously there is no algorithm
to compute it, so Lean will require you to mark any definition that would
involve executing `Classical.choice` or other axioms as `noncomputable`, and
will not produce any executable code for such definitions.
-/
axiom Classical.choice {α : Sort u} : Nonempty α → α

/--
The elimination principle for `Nonempty α`. If `Nonempty α`, and we can
prove `p` given any element `x : α`, then `p` holds. Note that it is essential
that `p` is a `Prop` here; the version with `p` being a `Sort u` is equivalent
to `Classical.choice`.
-/
protected theorem Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  match h₁ with
  | intro a => h₂ a

instance {α : Sort u} [Inhabited α] : Nonempty α :=
  ⟨default⟩

/--
A variation on `Classical.choice` that uses typeclass inference to
infer the proof of `Nonempty α`.
-/
noncomputable def Classical.ofNonempty {α : Sort u} [Nonempty α] : α :=
  Classical.choice inferInstance

instance {α : Sort u} {β : Sort v} [Nonempty β] : Nonempty (α → β) :=
  Nonempty.intro fun _ => Classical.ofNonempty

instance Pi.instNonempty {α : Sort u} {β : α → Sort v} [(a : α) → Nonempty (β a)] :
    Nonempty ((a : α) → β a) :=
  Nonempty.intro fun _ => Classical.ofNonempty

instance : Inhabited (Sort u) where
  default := PUnit

instance (α : Sort u) {β : Sort v} [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default

instance Pi.instInhabited {α : Sort u} {β : α → Sort v} [(a : α) → Inhabited (β a)] :
    Inhabited ((a : α) → β a) where
  default := fun _ => default

deriving instance Inhabited for Bool

/-- Universe lifting operation from `Sort u` to `Type u`. -/
structure PLift (α : Sort u) : Type u where
  /-- Lift a value into `PLift α` -/    up ::
  /-- Extract a value from `PLift α` -/ down : α

/-- Bijection between `α` and `PLift α` -/
theorem PLift.up_down {α : Sort u} (b : PLift α) : Eq (up (down b)) b := rfl

/-- Bijection between `α` and `PLift α` -/
theorem PLift.down_up {α : Sort u} (a : α) : Eq (down (up a)) a := rfl

/--
`NonemptyType.{u}` is the type of nonempty types in universe `u`.
It is mainly used in constant declarations where we wish to introduce a type
and simultaneously assert that it is nonempty, but otherwise make the type
opaque.
-/
def NonemptyType := Subtype fun α : Type u => Nonempty α

/-- The underlying type of a `NonemptyType`. -/
abbrev NonemptyType.type (type : NonemptyType.{u}) : Type u :=
  type.val

/-- `NonemptyType` is inhabited, because `PUnit` is a nonempty type. -/
instance : Inhabited NonemptyType.{u} where
  default := ⟨PUnit, ⟨⟨⟩⟩⟩

/--
Universe lifting operation from a lower `Type` universe to a higher one.
To express this using level variables, the input is `Type s` and the output is
`Type (max s r)`, so if `s ≤ r` then the latter is (definitionally) `Type r`.

The universe variable `r` is written first so that `ULift.{r} α` can be used
when `s` can be inferred from the type of `α`.
-/
structure ULift.{r, s} (α : Type s) : Type (max s r) where
  /-- Lift a value into `ULift α` -/    up ::
  /-- Extract a value from `ULift α` -/ down : α

/-- Bijection between `α` and `ULift.{v} α` -/
theorem ULift.up_down {α : Type u} (b : ULift.{v} α) : Eq (up (down b)) b := rfl

/-- Bijection between `α` and `ULift.{v} α` -/
theorem ULift.down_up {α : Type u} (a : α) : Eq (down (up.{v} a)) a := rfl

/--
`Decidable p` is a data-carrying class that supplies a proof that `p` is
either `true` or `false`. It is equivalent to `Bool` (and in fact it has the
same code generation as `Bool`) together with a proof that the `Bool` is
true iff `p` is.

`Decidable` instances are used to infer "computation strategies" for
propositions, so that you can have the convenience of writing propositions
inside `if` statements and executing them (which actually executes the inferred
decidability instance instead of the proposition, which has no code).

If a proposition `p` is `Decidable`, then `(by decide : p)` will prove it by
evaluating the decidability instance to `isTrue h` and returning `h`.

Because `Decidable` carries data,
when writing `@[simp]` lemmas which include a `Decidable` instance on the LHS,
it is best to use `{_ : Decidable p}` rather than `[Decidable p]`
so that non-canonical instances can be found via unification rather than
typeclass search.
-/
class inductive Decidable (p : Prop) where
  /-- Prove that `p` is decidable by supplying a proof of `¬p` -/
  | isFalse (h : Not p) : Decidable p
  /-- Prove that `p` is decidable by supplying a proof of `p` -/
  | isTrue (h : p) : Decidable p

/--
Convert a decidable proposition into a boolean value.

If `p : Prop` is decidable, then `decide p : Bool` is the boolean value
which is `true` if `p` is true and `false` if `p` is false.
-/
@[inline_if_reduce, nospecialize] def Decidable.decide (p : Prop) [h : Decidable p] : Bool :=
  h.casesOn (fun _ => false) (fun _ => true)

export Decidable (isTrue isFalse decide)

/-- A decidable predicate. See `Decidable`. -/
abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)

/-- A decidable relation. See `Decidable`. -/
abbrev DecidableRel {α : Sort u} {β : Sort v} (r : α → β → Prop) :=
  (a : α) → (b : β) → Decidable (r a b)

/--
Asserts that `α` has decidable equality, that is, `a = b` is decidable
for all `a b : α`. See `Decidable`.
-/
abbrev DecidableEq (α : Sort u) :=
  (a b : α) → Decidable (Eq a b)

/-- Proves that `a = b` is decidable given `DecidableEq α`. -/
def decEq {α : Sort u} [inst : DecidableEq α] (a b : α) : Decidable (Eq a b) :=
  inst a b

set_option linter.unusedVariables false in
theorem decide_eq_true : [inst : Decidable p] → p → Eq (decide p) true
  | isTrue  _, _   => rfl
  | isFalse h₁, h₂ => absurd h₂ h₁

theorem decide_eq_false : [Decidable p] → Not p → Eq (decide p) false
  | isTrue  h₁, h₂ => absurd h₁ h₂
  | isFalse _, _   => rfl

theorem of_decide_eq_true [inst : Decidable p] : Eq (decide p) true → p := fun h =>
  match (generalizing := false) inst with
  | isTrue  h₁ => h₁
  | isFalse h₁ => absurd h (ne_true_of_eq_false (decide_eq_false h₁))

theorem of_decide_eq_false [inst : Decidable p] : Eq (decide p) false → Not p := fun h =>
  match (generalizing := false) inst with
  | isTrue  h₁ => absurd h (ne_false_of_eq_true (decide_eq_true h₁))
  | isFalse h₁ => h₁

theorem of_decide_eq_self_eq_true [inst : DecidableEq α] (a : α) : Eq (decide (Eq a a)) true :=
  match (generalizing := false) inst a a with
  | isTrue  _  => rfl
  | isFalse h₁ => absurd rfl h₁

/-- Decidable equality for Bool -/
@[inline] def Bool.decEq (a b : Bool) : Decidable (Eq a b) :=
   match a, b with
   | false, false => isTrue rfl
   | false, true  => isFalse (fun h => Bool.noConfusion h)
   | true, false  => isFalse (fun h => Bool.noConfusion h)
   | true, true   => isTrue rfl

@[inline] instance : DecidableEq Bool :=
   Bool.decEq

/--
`BEq α` is a typeclass for supplying a boolean-valued equality relation on
`α`, notated as `a == b`. Unlike `DecidableEq α` (which uses `a = b`), this
is `Bool` valued instead of `Prop` valued, and it also does not have any
axioms like being reflexive or agreeing with `=`. It is mainly intended for
programming applications. See `LawfulBEq` for a version that requires that
`==` and `=` coincide.

Typically we prefer to put the "more variable" term on the left,
and the "more constant" term on the right.
-/
class BEq (α : Type u) where
  /-- Boolean equality, notated as `a == b`. -/
  beq : α → α → Bool

open BEq (beq)

instance [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)


/--
"Dependent" if-then-else, normally written via the notation `if h : c then t(h) else e(h)`,
is sugar for `dite c (fun h => t(h)) (fun h => e(h))`, and it is the same as
`if c then t else e` except that `t` is allowed to depend on a proof `h : c`,
and `e` can depend on `h : ¬c`. (Both branches use the same name for the hypothesis,
even though it has different types in the two cases.)

We use this to be able to communicate the if-then-else condition to the branches.
For example, `Array.get arr i h` expects a proof `h : i < arr.size` in order to
avoid a bounds check, so you can write `if h : i < arr.size then arr.get i h else ...`
to avoid the bounds check inside the if branch. (Of course in this case we have only
lifted the check into an explicit `if`, but we could also use this proof multiple times
or derive `i < arr.size` from some other proposition that we are checking in the `if`.)
-/
@[macro_inline] def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  h.casesOn e t

/-! # if-then-else -/

/--
`if c then t else e` is notation for `ite c t e`, "if-then-else", which decides to
return `t` or `e` depending on whether `c` is true or false. The explicit argument
`c : Prop` does not have any actual computational content, but there is an additional
`[Decidable c]` argument synthesized by typeclass inference which actually
determines how to evaluate `c` to true or false. Write `if h : c then t else e`
instead for a "dependent if-then-else" `dite`, which allows `t`/`e` to use the fact
that `c` is true/false.
-/
/-
Because Lean uses a strict (call-by-value) evaluation strategy, the signature of this
function is problematic in that it would require `t` and `e` to be evaluated before
calling the `ite` function, which would cause both sides of the `if` to be evaluated.
Even if the result is discarded, this would be a big performance problem,
and is undesirable for users in any case. To resolve this, `ite` is marked as
`@[macro_inline]`, which means that it is unfolded during code generation, and
the definition of the function uses `fun _ => t` and `fun _ => e` so this recovers
the expected "lazy" behavior of `if`: the `t` and `e` arguments delay evaluation
until `c` is known.
-/
@[macro_inline] def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  h.casesOn (fun _ => e) (fun _ => t)

@[macro_inline] instance {p q} [dp : Decidable p] [dq : Decidable q] : Decidable (And p q) :=
  match dp with
  | isTrue  hp =>
    match dq with
    | isTrue hq  => isTrue ⟨hp, hq⟩
    | isFalse hq => isFalse (fun h => hq (And.right h))
  | isFalse hp =>
    isFalse (fun h => hp (And.left h))

@[macro_inline] instance [dp : Decidable p] [dq : Decidable q] : Decidable (Or p q) :=
  match dp with
  | isTrue  hp => isTrue (Or.inl hp)
  | isFalse hp =>
    match dq with
    | isTrue hq  => isTrue (Or.inr hq)
    | isFalse hq =>
      isFalse fun h => match h with
        | Or.inl h => hp h
        | Or.inr h => hq h

instance [dp : Decidable p] : Decidable (Not p) :=
  match dp with
  | isTrue hp  => isFalse (absurd hp)
  | isFalse hp => isTrue hp

/-! # Boolean operators -/

/--
`cond b x y` is the same as `if b then x else y`, but optimized for a
boolean condition. It can also be written as `bif b then x else y`.
This is `@[macro_inline]` because `x` and `y` should not
be eagerly evaluated (see `ite`).
-/
@[macro_inline] def cond {α : Sort u} (c : Bool) (x y : α) : α :=
  match c with
  | true  => x
  | false => y


/--
`Bool.dcond b (fun h => x) (fun h => y)` is the same as `if h _ : b then x else y`,
but optimized for a boolean condition. It can also be written as `bif b then x else y`.
This is `@[macro_inline]` because `x` and `y` should not be eagerly evaluated (see `dite`).
This definition intendend for metaprogramming use, and does not come with a suitable API.
-/
@[macro_inline]
protected def Bool.dcond {α : Sort u} (c : Bool) (x : Eq c true → α) (y : Eq c false → α) : α :=
  match c with
  | true  => x rfl
  | false => y rfl

/--
`or x y`, or `x || y`, is the boolean "or" operation (not to be confused
with `Or : Prop → Prop → Prop`, which is the propositional connective).
It is `@[macro_inline]` because it has C-like short-circuiting behavior:
if `x` is true then `y` is not evaluated.
-/
@[macro_inline] def Bool.or (x y : Bool) : Bool :=
  match x with
  | true  => true
  | false => y

/--
`and x y`, or `x && y`, is the boolean "and" operation (not to be confused
with `And : Prop → Prop → Prop`, which is the propositional connective).
It is `@[macro_inline]` because it has C-like short-circuiting behavior:
if `x` is false then `y` is not evaluated.
-/
@[macro_inline] def Bool.and (x y : Bool) : Bool :=
  match x with
  | false => false
  | true  => y

/--
`not x`, or `!x`, is the boolean "not" operation (not to be confused
with `Not : Prop → Prop`, which is the propositional connective).
-/
@[inline] def Bool.not : Bool → Bool
  | true  => false
  | false => true

export Bool (or and not)

/--
The type of natural numbers, starting at zero. It is defined as an
inductive type freely generated by "zero is a natural number" and
"the successor of a natural number is a natural number".

You can prove a theorem `P n` about `n : Nat` by `induction n`, which will
expect a proof of the theorem for `P 0`, and a proof of `P (succ i)` assuming
a proof of `P i`. The same method also works to define functions by recursion
on natural numbers: induction and recursion are two expressions of the same
operation from Lean's point of view.

```
open Nat
example (n : Nat) : n < succ n := by
  induction n with
  | zero =>
    show 0 < 1
    decide
  | succ i ih => -- ih : i < succ i
    show succ i < succ (succ i)
    exact Nat.succ_lt_succ ih
```

This type is special-cased by both the kernel and the compiler:
* The type of expressions contains "`Nat` literals" as a primitive constructor,
  and the kernel knows how to reduce zero/succ expressions to nat literals.
* If implemented naively, this type would represent a numeral `n` in unary as a
  linked list with `n` links, which is horribly inefficient. Instead, the
  runtime itself has a special representation for `Nat` which stores numbers up
  to 2^63 directly and larger numbers use an arbitrary precision "bignum"
  library (usually [GMP](https://gmplib.org/)).
-/
inductive Nat where
  /-- `Nat.zero`, is the smallest natural number. This is one of the two
  constructors of `Nat`. Using `Nat.zero` should usually be avoided in favor of
  `0 : Nat` or simply `0`, in order to remain compatible with the simp normal
  form defined by `Nat.zero_eq`. -/
  | zero : Nat
  /-- The successor function on natural numbers, `succ n = n + 1`.
  This is one of the two constructors of `Nat`. Using `succ n` should usually
  be avoided in favor of `n + 1`, in order to remain compatible with the simp
  normal form defined by `Nat.succ_eq_add_one`. -/
  | succ (n : Nat) : Nat

instance : Inhabited Nat where
  default := Nat.zero

/--
The class `OfNat α n` powers the numeric literal parser. If you write
`37 : α`, Lean will attempt to synthesize `OfNat α 37`, and will generate
the term `(OfNat.ofNat 37 : α)`.

There is a bit of infinite regress here since the desugaring apparently
still contains a literal `37` in it. The type of expressions contains a
primitive constructor for "raw natural number literals", which you can directly
access using the macro `nat_lit 37`. Raw number literals are always of type `Nat`.
So it would be more correct to say that Lean looks for an instance of
`OfNat α (nat_lit 37)`, and it generates the term `(OfNat.ofNat (nat_lit 37) : α)`.
-/
class OfNat (α : Type u) (_ : Nat) where
  /-- The `OfNat.ofNat` function is automatically inserted by the parser when
  the user writes a numeric literal like `1 : α`. Implementations of this
  typeclass can therefore customize the behavior of `n : α` based on `n` and
  `α`. -/
  ofNat : α

@[default_instance 100] /- low prio -/
instance instOfNatNat (n : Nat) : OfNat Nat n where
  ofNat := n

/-- `LE α` is the typeclass which supports the notation `x ≤ y` where `x y : α`.-/
class LE (α : Type u) where
  /-- The less-equal relation: `x ≤ y` -/
  le : α → α → Prop

/-- `LT α` is the typeclass which supports the notation `x < y` where `x y : α`.-/
class LT (α : Type u) where
  /-- The less-than relation: `x < y` -/
  lt : α → α → Prop

/-- `a ≥ b` is an abbreviation for `b ≤ a`. -/
@[reducible] def GE.ge {α : Type u} [LE α] (a b : α) : Prop := LE.le b a
/-- `a > b` is an abbreviation for `b < a`. -/
@[reducible] def GT.gt {α : Type u} [LT α] (a b : α) : Prop := LT.lt b a

/-- Abbreviation for `DecidableRel (· < · : α → α → Prop)`. -/
abbrev DecidableLT (α : Type u) [LT α] := DecidableRel (LT.lt : α → α → Prop)
/-- Abbreviation for `DecidableRel (· ≤ · : α → α → Prop)`. -/
abbrev DecidableLE (α : Type u) [LE α] := DecidableRel (LE.le : α → α → Prop)

/-- `Max α` is the typeclass which supports the operation `max x y` where `x y : α`.-/
class Max (α : Type u) where
  /-- The maximum operation: `max x y`. -/
  max : α → α → α

export Max (max)

/-- Implementation of the `max` operation using `≤`. -/
-- Marked inline so that `min x y + max x y` can be optimized to a single branch.
@[inline]
def maxOfLe [LE α] [DecidableRel (@LE.le α _)] : Max α where
  max x y := ite (LE.le x y) y x

/-- `Min α` is the typeclass which supports the operation `min x y` where `x y : α`.-/
class Min (α : Type u) where
  /-- The minimum operation: `min x y`. -/
  min : α → α → α

export Min (min)

/-- Implementation of the `min` operation using `≤`. -/
-- Marked inline so that `min x y + max x y` can be optimized to a single branch.
@[inline]
def minOfLe [LE α] [DecidableRel (@LE.le α _)] : Min α where
  min x y := ite (LE.le x y) x y

/--
Transitive chaining of proofs, used e.g. by `calc`.

It takes two relations `r` and `s` as "input", and produces an "output"
relation `t`, with the property that `r a b` and `s b c` implies `t a c`.
The `calc` tactic uses this so that when it sees a chain with `a ≤ b` and `b < c`
it knows that this should be a proof of `a < c` because there is an instance
`Trans (·≤·) (·<·) (·<·)`.
-/
class Trans (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) where
  /-- Compose two proofs by transitivity, generalized over the relations involved. -/
  trans : r a b → s b c → t a c

export Trans (trans)

instance (r : α → γ → Sort u) : Trans Eq r r where
  trans heq h' := heq ▸ h'

instance (r : α → β → Sort u) : Trans r Eq r where
  trans h' heq := heq ▸ h'

/--
The notation typeclass for heterogeneous addition.
This enables the notation `a + b : γ` where `a : α`, `b : β`.
-/
class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a + b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hAdd : α → β → γ

/--
The notation typeclass for heterogeneous subtraction.
This enables the notation `a - b : γ` where `a : α`, `b : β`.
-/
class HSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a - b` computes the difference of `a` and `b`.
  The meaning of this notation is type-dependent.
  * For natural numbers, this operator saturates at 0: `a - b = 0` when `a ≤ b`. -/
  hSub : α → β → γ

/--
The notation typeclass for heterogeneous multiplication.
This enables the notation `a * b : γ` where `a : α`, `b : β`.
-/
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a * b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hMul : α → β → γ

/--
The notation typeclass for heterogeneous division.
This enables the notation `a / b : γ` where `a : α`, `b : β`.
-/
class HDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a / b` computes the result of dividing `a` by `b`.
  The meaning of this notation is type-dependent.
  * For most types like `Nat`, `Int`, `Rat`, `Real`, `a / 0` is defined to be `0`.
  * For `Nat`, `a / b` rounds downwards.
  * For `Int`, `a / b` rounds downwards if `b` is positive or upwards if `b` is negative.
    It is implemented as `Int.ediv`, the unique function satisfying
    `a % b + b * (a / b) = a` and `0 ≤ a % b < natAbs b` for `b ≠ 0`.
    Other rounding conventions are available using the functions
    `Int.fdiv` (floor rounding) and `Int.tdiv` (truncation rounding).
  * For `Float`, `a / 0` follows the IEEE 754 semantics for division,
    usually resulting in `inf` or `nan`. -/
  hDiv : α → β → γ

/--
The notation typeclass for heterogeneous modulo / remainder.
This enables the notation `a % b : γ` where `a : α`, `b : β`.
-/
class HMod (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a % b` computes the remainder upon dividing `a` by `b`.
  The meaning of this notation is type-dependent.
  * For `Nat` and `Int` it satisfies `a % b + b * (a / b) = a`,
    and `a % 0` is defined to be `a`. -/
  hMod : α → β → γ

/--
The notation typeclass for heterogeneous exponentiation.
This enables the notation `a ^ b : γ` where `a : α`, `b : β`.
-/
class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ^ b` computes `a` to the power of `b`.
  The meaning of this notation is type-dependent. -/
  hPow : α → β → γ

/--
The notation typeclass for heterogeneous append.
This enables the notation `a ++ b : γ` where `a : α`, `b : β`.
-/
class HAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ++ b` is the result of concatenation of `a` and `b`, usually read "append".
  The meaning of this notation is type-dependent. -/
  hAppend : α → β → γ

/--
The typeclass behind the notation `a <|> b : γ` where `a : α`, `b : β`.
Because `b` is "lazy" in this notation, it is passed as `Unit → β` to the
implementation so it can decide when to evaluate it.
-/
class HOrElse (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a <|> b` executes `a` and returns the result, unless it fails in which
  case it executes and returns `b`. Because `b` is not always executed, it
  is passed as a thunk so it can be forced only when needed.
  The meaning of this notation is type-dependent. -/
  hOrElse : α → (Unit → β) → γ

/--
The typeclass behind the notation `a >> b : γ` where `a : α`, `b : β`.
Because `b` is "lazy" in this notation, it is passed as `Unit → β` to the
implementation so it can decide when to evaluate it.
-/
class HAndThen (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a >> b` executes `a`, ignores the result, and then executes `b`.
  If `a` fails then `b` is not executed. Because `b` is not always executed, it
  is passed as a thunk so it can be forced only when needed.
  The meaning of this notation is type-dependent. -/
  hAndThen : α → (Unit → β) → γ

/-- The typeclass behind the notation `a &&& b : γ` where `a : α`, `b : β`. -/
class HAnd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a &&& b` computes the bitwise AND of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hAnd : α → β → γ

/-- The typeclass behind the notation `a ^^^ b : γ` where `a : α`, `b : β`. -/
class HXor (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ^^^ b` computes the bitwise XOR of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hXor : α → β → γ

/-- The typeclass behind the notation `a ||| b : γ` where `a : α`, `b : β`. -/
class HOr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ||| b` computes the bitwise OR of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hOr : α → β → γ

/-- The typeclass behind the notation `a <<< b : γ` where `a : α`, `b : β`. -/
class HShiftLeft (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a <<< b` computes `a` shifted to the left by `b` places.
  The meaning of this notation is type-dependent.
  * On `Nat`, this is equivalent to `a * 2 ^ b`.
  * On `UInt8` and other fixed width unsigned types, this is the same but
    truncated to the bit width. -/
  hShiftLeft : α → β → γ

/-- The typeclass behind the notation `a >>> b : γ` where `a : α`, `b : β`. -/
class HShiftRight (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a >>> b` computes `a` shifted to the right by `b` places.
  The meaning of this notation is type-dependent.
  * On `Nat` and fixed width unsigned types like `UInt8`,
    this is equivalent to `a / 2 ^ b`. -/
  hShiftRight : α → β → γ

/-- A type with a zero element. -/
class Zero (α : Type u) where
  /-- The zero element of the type. -/
  zero : α

/-- The homogeneous version of `HAdd`: `a + b : α` where `a b : α`. -/
class Add (α : Type u) where
  /-- `a + b` computes the sum of `a` and `b`. See `HAdd`. -/
  add : α → α → α

/-- The homogeneous version of `HSub`: `a - b : α` where `a b : α`. -/
class Sub (α : Type u) where
  /-- `a - b` computes the difference of `a` and `b`. See `HSub`. -/
  sub : α → α → α

/-- The homogeneous version of `HMul`: `a * b : α` where `a b : α`. -/
class Mul (α : Type u) where
  /-- `a * b` computes the product of `a` and `b`. See `HMul`. -/
  mul : α → α → α

/--
The notation typeclass for negation.
This enables the notation `-a : α` where `a : α`.
-/
class Neg (α : Type u) where
  /-- `-a` computes the negative or opposite of `a`.
  The meaning of this notation is type-dependent. -/
  neg : α → α

/-- The homogeneous version of `HDiv`: `a / b : α` where `a b : α`. -/
class Div (α : Type u) where
  /-- `a / b` computes the result of dividing `a` by `b`. See `HDiv`. -/
  div : α → α → α

/-- The homogeneous version of `HMod`: `a % b : α` where `a b : α`. -/
class Mod (α : Type u) where
  /-- `a % b` computes the remainder upon dividing `a` by `b`. See `HMod`. -/
  mod : α → α → α

/-- Notation typeclass for the `∣` operation (typed as `\|`), which represents divisibility. -/
class Dvd (α : Type _) where
  /-- Divisibility. `a ∣ b` (typed as `\|`) means that there is some `c` such that `b = a * c`. -/
  dvd : α → α → Prop

/--
The homogeneous version of `HPow`: `a ^ b : α` where `a : α`, `b : β`.
(The right argument is not the same as the left since we often want this even
in the homogeneous case.)

Types can choose to subscribe to particular defaulting behavior by providing
an instance to either `NatPow` or `HomogeneousPow`:
- `NatPow` is for types whose exponents is preferentially a `Nat`.
- `HomogeneousPow` is for types whose base and exponent are preferentially the same.
-/
class Pow (α : Type u) (β : Type v) where
  /-- `a ^ b` computes `a` to the power of `b`. See `HPow`. -/
  pow : α → β → α

/-- The homogeneous version of `Pow` where the exponent is a `Nat`.
The purpose of this class is that it provides a default `Pow` instance,
which can be used to specialize the exponent to `Nat` during elaboration.

For example, if `x ^ 2` should preferentially elaborate with `2 : Nat` then `x`'s type should
provide an instance for this class. -/
class NatPow (α : Type u) where
  /-- `a ^ n` computes `a` to the power of `n` where `n : Nat`. See `Pow`. -/
  protected pow : α → Nat → α

/-- The completely homogeneous version of `Pow` where the exponent has the same type as the base.
The purpose of this class is that it provides a default `Pow` instance,
which can be used to specialize the exponent to have the same type as the base's type during elaboration.
This is to say, a type should provide an instance for this class in case `x ^ y` should be elaborated
with both `x` and `y` having the same type.

For example, the `Float` type provides an instance of this class, which causes expressions
such as `(2.2 ^ 2.2 : Float)` to elaborate. -/
class HomogeneousPow (α : Type u) where
  /-- `a ^ b` computes `a` to the power of `b` where `a` and `b` both have the same type. -/
  protected pow : α → α → α

/-- The homogeneous version of `HAppend`: `a ++ b : α` where `a b : α`. -/
class Append (α : Type u) where
  /-- `a ++ b` is the result of concatenation of `a` and `b`. See `HAppend`. -/
  append : α → α → α

/--
The homogeneous version of `HOrElse`: `a <|> b : α` where `a b : α`.
Because `b` is "lazy" in this notation, it is passed as `Unit → α` to the
implementation so it can decide when to evaluate it.
-/
class OrElse (α : Type u) where
  /-- The implementation of `a <|> b : α`. See `HOrElse`. -/
  orElse  : α → (Unit → α) → α

/--
The homogeneous version of `HAndThen`: `a >> b : α` where `a b : α`.
Because `b` is "lazy" in this notation, it is passed as `Unit → α` to the
implementation so it can decide when to evaluate it.
-/
class AndThen (α : Type u) where
  /-- The implementation of `a >> b : α`. See `HAndThen`. -/
  andThen : α → (Unit → α) → α

/--
The homogeneous version of `HAnd`: `a &&& b : α` where `a b : α`.
(It is called `AndOp` because `And` is taken for the propositional connective.)
-/
class AndOp (α : Type u) where
  /-- The implementation of `a &&& b : α`. See `HAnd`. -/
  and : α → α → α

/-- The homogeneous version of `HXor`: `a ^^^ b : α` where `a b : α`. -/
class Xor (α : Type u) where
  /-- The implementation of `a ^^^ b : α`. See `HXor`. -/
  xor : α → α → α

/--
The homogeneous version of `HOr`: `a ||| b : α` where `a b : α`.
(It is called `OrOp` because `Or` is taken for the propositional connective.)
-/
class OrOp (α : Type u) where
  /-- The implementation of `a ||| b : α`. See `HOr`. -/
  or : α → α → α

/-- The typeclass behind the notation `~~~a : α` where `a : α`. -/
class Complement (α : Type u) where
  /-- The implementation of `~~~a : α`. -/
  complement : α → α

/-- The homogeneous version of `HShiftLeft`: `a <<< b : α` where `a b : α`. -/
class ShiftLeft (α : Type u) where
  /-- The implementation of `a <<< b : α`. See `HShiftLeft`. -/
  shiftLeft : α → α → α

/-- The homogeneous version of `HShiftRight`: `a >>> b : α` where `a b : α`. -/
class ShiftRight (α : Type u) where
  /-- The implementation of `a >>> b : α`. See `HShiftRight`. -/
  shiftRight : α → α → α

@[default_instance]
instance instHAdd [Add α] : HAdd α α α where
  hAdd a b := Add.add a b

@[default_instance]
instance instHSub [Sub α] : HSub α α α where
  hSub a b := Sub.sub a b

@[default_instance]
instance instHMul [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

@[default_instance]
instance instHDiv [Div α] : HDiv α α α where
  hDiv a b := Div.div a b

@[default_instance]
instance instHMod [Mod α] : HMod α α α where
  hMod a b := Mod.mod a b

@[default_instance]
instance instHPow [Pow α β] : HPow α β α where
  hPow a b := Pow.pow a b

@[default_instance]
instance instPowNat [NatPow α] : Pow α Nat where
  pow a n := NatPow.pow a n

@[default_instance]
instance [HomogeneousPow α] : Pow α α where
  pow a b := HomogeneousPow.pow a b

@[default_instance]
instance [Append α] : HAppend α α α where
  hAppend a b := Append.append a b

@[default_instance]
instance [OrElse α] : HOrElse α α α where
  hOrElse a b := OrElse.orElse a b

@[default_instance]
instance [AndThen α] : HAndThen α α α where
  hAndThen a b := AndThen.andThen a b

@[default_instance]
instance [AndOp α] : HAnd α α α where
  hAnd a b := AndOp.and a b

@[default_instance]
instance [Xor α] : HXor α α α where
  hXor a b := Xor.xor a b

@[default_instance]
instance [OrOp α] : HOr α α α where
  hOr a b := OrOp.or a b

@[default_instance]
instance [ShiftLeft α] : HShiftLeft α α α where
  hShiftLeft a b := ShiftLeft.shiftLeft a b

@[default_instance]
instance [ShiftRight α] : HShiftRight α α α where
  hShiftRight a b := ShiftRight.shiftRight a b

open HAdd (hAdd)
open HSub (hSub)
open HMul (hMul)
open HPow (hPow)
open HAppend (hAppend)

/--
The typeclass behind the notation `a ∈ s : Prop` where `a : α`, `s : γ`.
Because `α` is an `outParam`, the "container type" `γ` determines the type
of the elements of the container.
-/
class Membership (α : outParam (Type u)) (γ : Type v) where
  /-- The membership relation `a ∈ s : Prop` where `a : α`, `s : γ`. -/
  mem : γ → α → Prop

set_option bootstrap.genMatcherCode false in
/--
Addition of natural numbers.

This definition is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model (and it is soundness-critical that they coincide).
-/
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

instance instAddNat : Add Nat where
  add := Nat.add

/- We mark the following definitions as pattern to make sure they can be used in recursive equations,
   and reduced by the equation Compiler. -/
attribute [match_pattern] Nat.add Add.add HAdd.hAdd Neg.neg Mul.mul HMul.hMul

set_option bootstrap.genMatcherCode false in
/--
Multiplication of natural numbers.

This definition is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model (and it is soundness-critical that they coincide).
-/
@[extern "lean_nat_mul"]
protected def Nat.mul : (@& Nat) → (@& Nat) → Nat
  | _, 0          => 0
  | a, Nat.succ b => Nat.add (Nat.mul a b) a

instance instMulNat : Mul Nat where
  mul := Nat.mul

set_option bootstrap.genMatcherCode false in
/--
The power operation on natural numbers.

This definition is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model.
-/
@[extern "lean_nat_pow"]
protected def Nat.pow (m : @& Nat) : (@& Nat) → Nat
  | 0      => 1
  | succ n => Nat.mul (Nat.pow m n) m

instance instNatPowNat : NatPow Nat := ⟨Nat.pow⟩

set_option bootstrap.genMatcherCode false in
/--
(Boolean) equality of natural numbers.

This definition is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model (and it is soundness-critical that they coincide).
-/
@[extern "lean_nat_dec_eq"]
def Nat.beq : (@& Nat) → (@& Nat) → Bool
  | zero,   zero   => true
  | zero,   succ _ => false
  | succ _, zero   => false
  | succ n, succ m => beq n m

theorem Nat.eq_of_beq_eq_true : {n m : Nat} → Eq (beq n m) true → Eq n m
  | zero,   zero,   _ => rfl
  | zero,   succ _, h => Bool.noConfusion h
  | succ _, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have : Eq (beq n m) true := h
    have : Eq n m := eq_of_beq_eq_true this
    this ▸ rfl

theorem Nat.ne_of_beq_eq_false : {n m : Nat} → Eq (beq n m) false → Not (Eq n m)
  | zero,   zero,   h₁, _  => Bool.noConfusion h₁
  | zero,   succ _, _,  h₂ => Nat.noConfusion h₂
  | succ _, zero,   _,  h₂ => Nat.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have : Eq (beq n m) false := h₁
    Nat.noConfusion h₂ (fun h₂ => absurd h₂ (ne_of_beq_eq_false this))

/--
A decision procedure for equality of natural numbers.

This definition is overridden in the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model.
-/
@[reducible, extern "lean_nat_dec_eq"]
protected def Nat.decEq (n m : @& Nat) : Decidable (Eq n m) :=
  match h:beq n m with
  | true  => isTrue (eq_of_beq_eq_true h)
  | false => isFalse (ne_of_beq_eq_false h)

@[inline] instance : DecidableEq Nat := Nat.decEq

set_option bootstrap.genMatcherCode false in
/--
The (Boolean) less-equal relation on natural numbers.

This definition is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model (and it is soundness-critical that they coincide).
-/
@[extern "lean_nat_dec_le"]
def Nat.ble : @& Nat → @& Nat → Bool
  | zero,   zero   => true
  | zero,   succ _ => true
  | succ _, zero   => false
  | succ n, succ m => ble n m

/--
An inductive definition of the less-equal relation on natural numbers,
characterized as the least relation `≤` such that `n ≤ n` and `n ≤ m → n ≤ m + 1`.
-/
protected inductive Nat.le (n : Nat) : Nat → Prop
  /-- Less-equal is reflexive: `n ≤ n` -/
  | refl     : Nat.le n n
  /-- If `n ≤ m`, then `n ≤ m + 1`. -/
  | step {m} : Nat.le n m → Nat.le n (succ m)

instance instLENat : LE Nat where
  le := Nat.le

/-- The strict less than relation on natural numbers is defined as `n < m := n + 1 ≤ m`. -/
protected def Nat.lt (n m : Nat) : Prop :=
  Nat.le (succ n) m

instance instLTNat : LT Nat where
  lt := Nat.lt

theorem Nat.not_succ_le_zero : ∀ (n : Nat), LE.le (succ n) 0 → False
  | 0      => nofun
  | succ _ => nofun

theorem Nat.not_lt_zero (n : Nat) : Not (LT.lt n 0) :=
  not_succ_le_zero n

theorem Nat.zero_le : (n : Nat) → LE.le 0 n
  | zero   => Nat.le.refl
  | succ n => Nat.le.step (zero_le n)

theorem Nat.succ_le_succ : LE.le n m → LE.le (succ n) (succ m)
  | Nat.le.refl   => Nat.le.refl
  | Nat.le.step h => Nat.le.step (succ_le_succ h)

theorem Nat.zero_lt_succ (n : Nat) : LT.lt 0 (succ n) :=
  succ_le_succ (zero_le n)

theorem Nat.le_step (h : LE.le n m) : LE.le n (succ m) :=
  Nat.le.step h

protected theorem Nat.le_trans {n m k : Nat} : LE.le n m → LE.le m k → LE.le n k
  | h,  Nat.le.refl    => h
  | h₁, Nat.le.step h₂ => Nat.le.step (Nat.le_trans h₁ h₂)

protected theorem Nat.lt_trans {n m k : Nat} (h₁ : LT.lt n m) : LT.lt m k → LT.lt n k :=
  Nat.le_trans (le_step h₁)

theorem Nat.le_succ (n : Nat) : LE.le n (succ n) :=
  Nat.le.step Nat.le.refl

theorem Nat.le_succ_of_le {n m : Nat} (h : LE.le n m) : LE.le n (succ m) :=
  Nat.le_trans h (le_succ m)

protected theorem Nat.le_refl (n : Nat) : LE.le n n :=
  Nat.le.refl

theorem Nat.succ_pos (n : Nat) : LT.lt 0 (succ n) :=
  zero_lt_succ n

set_option bootstrap.genMatcherCode false in
/--
The predecessor function on natural numbers.

This definition is overridden in the compiler to use `n - 1` instead.
The definition provided here is the logical model.
-/
@[extern "lean_nat_pred"]
def Nat.pred : (@& Nat) → Nat
  | 0      => 0
  | succ a => a

theorem Nat.pred_le_pred : {n m : Nat} → LE.le n m → LE.le (pred n) (pred m)
  | _,           _, Nat.le.refl   => Nat.le.refl
  | 0,      succ _, Nat.le.step h => h
  | succ _, succ _, Nat.le.step h => Nat.le_trans (le_succ _) h

theorem Nat.le_of_succ_le_succ {n m : Nat} : LE.le (succ n) (succ m) → LE.le n m :=
  pred_le_pred

theorem Nat.le_of_lt_succ {m n : Nat} : LT.lt m (succ n) → LE.le m n :=
  le_of_succ_le_succ

protected theorem Nat.eq_or_lt_of_le : {n m: Nat} → LE.le n m → Or (Eq n m) (LT.lt n m)
  | zero,   zero,   _ => Or.inl rfl
  | zero,   succ _, _ => Or.inr (Nat.succ_le_succ (Nat.zero_le _))
  | succ _, zero,   h => absurd h (not_succ_le_zero _)
  | succ n, succ m, h =>
    have : LE.le n m := Nat.le_of_succ_le_succ h
    match Nat.eq_or_lt_of_le this with
    | Or.inl h => Or.inl (h ▸ rfl)
    | Or.inr h => Or.inr (succ_le_succ h)

protected theorem Nat.lt_or_ge (n m : Nat) : Or (LT.lt n m) (GE.ge n m) :=
  match m with
  | zero   => Or.inr (zero_le n)
  | succ m =>
    match Nat.lt_or_ge n m with
    | Or.inl h => Or.inl (le_succ_of_le h)
    | Or.inr h =>
      match Nat.eq_or_lt_of_le h with
      | Or.inl h1 => Or.inl (h1 ▸ Nat.le_refl _)
      | Or.inr h1 => Or.inr h1

theorem Nat.not_succ_le_self : (n : Nat) → Not (LE.le (succ n) n)
  | 0      => not_succ_le_zero _
  | succ n => fun h => absurd (le_of_succ_le_succ h) (not_succ_le_self n)

protected theorem Nat.lt_irrefl (n : Nat) : Not (LT.lt n n) :=
  Nat.not_succ_le_self n

protected theorem Nat.lt_of_le_of_lt {n m k : Nat} (h₁ : LE.le n m) (h₂ : LT.lt m k) : LT.lt n k :=
  Nat.le_trans (Nat.succ_le_succ h₁) h₂

protected theorem Nat.le_antisymm {n m : Nat} (h₁ : LE.le n m) (h₂ : LE.le m n) : Eq n m :=
  match h₁ with
  | Nat.le.refl   => rfl
  | Nat.le.step h => absurd (Nat.lt_of_le_of_lt h h₂) (Nat.lt_irrefl n)

protected theorem Nat.lt_of_le_of_ne {n m : Nat} (h₁ : LE.le n m) (h₂ : Not (Eq n m)) : LT.lt n m :=
  match Nat.lt_or_ge n m with
  | Or.inl h₃ => h₃
  | Or.inr h₃ => absurd (Nat.le_antisymm h₁ h₃) h₂

theorem Nat.le_of_ble_eq_true (h : Eq (Nat.ble n m) true) : LE.le n m :=
  match n, m with
  | 0,      _      => Nat.zero_le _
  | succ _, succ _ => Nat.succ_le_succ (le_of_ble_eq_true h)

theorem Nat.ble_self_eq_true : (n : Nat) → Eq (Nat.ble n n) true
  | 0      => rfl
  | succ n => ble_self_eq_true n

theorem Nat.ble_succ_eq_true : {n m : Nat} → Eq (Nat.ble n m) true → Eq (Nat.ble n (succ m)) true
  | 0,      _,      _ => rfl
  | succ n, succ _, h => ble_succ_eq_true (n := n) h

theorem Nat.ble_eq_true_of_le (h : LE.le n m) : Eq (Nat.ble n m) true :=
  match h with
  | Nat.le.refl   => Nat.ble_self_eq_true n
  | Nat.le.step h => Nat.ble_succ_eq_true (ble_eq_true_of_le h)

theorem Nat.not_le_of_not_ble_eq_true (h : Not (Eq (Nat.ble n m) true)) : Not (LE.le n m) :=
  fun h' => absurd (Nat.ble_eq_true_of_le h') h

@[extern "lean_nat_dec_le"]
instance Nat.decLe (n m : @& Nat) : Decidable (LE.le n m) :=
  dite (Eq (Nat.ble n m) true) (fun h => isTrue (Nat.le_of_ble_eq_true h)) (fun h => isFalse (Nat.not_le_of_not_ble_eq_true h))

@[extern "lean_nat_dec_lt"]
instance Nat.decLt (n m : @& Nat) : Decidable (LT.lt n m) :=
  decLe (succ n) m

instance : Min Nat := minOfLe

set_option bootstrap.genMatcherCode false in
/--
(Truncated) subtraction of natural numbers. Because natural numbers are not
closed under subtraction, we define `n - m` to be `0` when `n < m`.

This definition is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model (and it is soundness-critical that they coincide).
-/
@[extern "lean_nat_sub"]
protected def Nat.sub : (@& Nat) → (@& Nat) → Nat
  | a, 0      => a
  | a, succ b => pred (Nat.sub a b)

instance instSubNat : Sub Nat where
  sub := Nat.sub

/--
Gets the word size of the platform. That is, whether the platform is 64 or 32 bits.

This function is opaque because we cannot guarantee at compile time that the target
will have the same size as the host, and also because we would like to avoid
typechecking being architecture-dependent. Nevertheless, Lean only works on
64 and 32 bit systems so we can encode this as a fact available for proof purposes.
-/
@[extern "lean_system_platform_nbits"] opaque System.Platform.getNumBits : Unit → Subtype fun (n : Nat) => Or (Eq n 32) (Eq n 64) :=
  fun _ => ⟨64, Or.inr rfl⟩ -- inhabitant

/-- Gets the word size of the platform. That is, whether the platform is 64 or 32 bits. -/
def System.Platform.numBits : Nat :=
  (getNumBits ()).val

theorem System.Platform.numBits_eq : Or (Eq numBits 32) (Eq numBits 64) :=
  (getNumBits ()).property

/--
`Fin n` is a natural number `i` with the constraint that `0 ≤ i < n`.
It is the "canonical type with `n` elements".
-/
@[pp_using_anonymous_constructor]
structure Fin (n : Nat) where
  /-- Creates a `Fin n` from `i : Nat` and a proof that `i < n`. -/
  mk ::
  /-- If `i : Fin n`, then `i.val : ℕ` is the described number. It can also be
  written as `i.1` or just `i` when the target type is known. -/
  val  : Nat
  /-- If `i : Fin n`, then `i.2` is a proof that `i.1 < n`. -/
  isLt : LT.lt val n

attribute [coe] Fin.val

theorem Fin.eq_of_val_eq {n} : ∀ {i j : Fin n}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Fin.val_eq_of_eq {n} {i j : Fin n} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

instance (n : Nat) : DecidableEq (Fin n) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (Fin.eq_of_val_eq h)
    | isFalse h => isFalse (fun h' => absurd (Fin.val_eq_of_eq h') h)

instance {n} : LT (Fin n) where
  lt a b := LT.lt a.val b.val

instance {n} : LE (Fin n) where
  le a b := LE.le a.val b.val

instance Fin.decLt {n} (a b : Fin n) : Decidable (LT.lt a b) := Nat.decLt ..
instance Fin.decLe {n} (a b : Fin n) : Decidable (LE.le a b) := Nat.decLe ..

/--
A bitvector of the specified width.

This is represented as the underlying `Nat` number in both the runtime
and the kernel, inheriting all the special support for `Nat`.
-/
structure BitVec (w : Nat) where
  /-- Construct a `BitVec w` from a number less than `2^w`.
  O(1), because we use `Fin` as the internal representation of a bitvector. -/
  ofFin ::
  /-- Interpret a bitvector as a number less than `2^w`.
  O(1), because we use `Fin` as the internal representation of a bitvector. -/
  toFin : Fin (hPow 2 w)

/--
Bitvectors have decidable equality. This should be used via the instance `DecidableEq (BitVec n)`.
-/
-- We manually derive the `DecidableEq` instances for `BitVec` because
-- we want to have builtin support for bit-vector literals, and we
-- need a name for this function to implement `canUnfoldAtMatcher` at `WHNF.lean`.
def BitVec.decEq (x y : BitVec n) : Decidable (Eq x y) :=
  match x, y with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => BitVec.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq (BitVec n) := BitVec.decEq

/-- The `BitVec` with value `i`, given a proof that `i < 2^n`. -/
@[match_pattern]
protected def BitVec.ofNatLT {n : Nat} (i : Nat) (p : LT.lt i (hPow 2 n)) : BitVec n where
  toFin := ⟨i, p⟩

/-- Given a bitvector `x`, return the underlying `Nat`. This is O(1) because `BitVec` is a
(zero-cost) wrapper around a `Nat`. -/
protected def BitVec.toNat (x : BitVec n) : Nat := x.toFin.val

instance : LT (BitVec n) where lt := (LT.lt ·.toNat ·.toNat)
instance (x y : BitVec n) : Decidable (LT.lt x y) :=
  inferInstanceAs (Decidable (LT.lt x.toNat y.toNat))

instance : LE (BitVec n) where le := (LE.le ·.toNat ·.toNat)
instance (x y : BitVec n) : Decidable (LE.le x y) :=
  inferInstanceAs (Decidable (LE.le x.toNat y.toNat))

/-- The size of type `UInt8`, that is, `2^8 = 256`. -/
abbrev UInt8.size : Nat := 256

/--
The type of unsigned 8-bit integers. This type has special support in the
compiler to make it actually 8 bits rather than wrapping a `Nat`.
-/
structure UInt8 where
  /--
  Create a `UInt8` from a `BitVec 8`. This function is overridden with a native implementation.
  -/
  ofBitVec ::
  /--
  Unpack a `UInt8` as a `BitVec 8`. This function is overridden with a native implementation.
  -/
  toBitVec : BitVec 8

attribute [extern "lean_uint8_of_nat_mk"] UInt8.ofBitVec
attribute [extern "lean_uint8_to_nat"] UInt8.toBitVec

/--
Pack a `Nat` less than `2^8` into a `UInt8`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint8_of_nat"]
def UInt8.ofNatLT (n : @& Nat) (h : LT.lt n UInt8.size) : UInt8 where
  toBitVec := BitVec.ofNatLT n h

set_option bootstrap.genMatcherCode false in
/--
Decides equality on `UInt8`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint8_dec_eq"]
def UInt8.decEq (a b : UInt8) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => UInt8.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt8 := UInt8.decEq

instance : Inhabited UInt8 where
  default := UInt8.ofNatLT 0 (of_decide_eq_true rfl)

/-- The size of type `UInt16`, that is, `2^16 = 65536`. -/
abbrev UInt16.size : Nat := 65536

/--
The type of unsigned 16-bit integers. This type has special support in the
compiler to make it actually 16 bits rather than wrapping a `Nat`.
-/
structure UInt16 where
  /--
  Create a `UInt16` from a `BitVec 16`. This function is overridden with a native implementation.
  -/
  ofBitVec ::
  /--
  Unpack a `UInt16` as a `BitVec 16`. This function is overridden with a native implementation.
  -/
  toBitVec : BitVec 16

attribute [extern "lean_uint16_of_nat_mk"] UInt16.ofBitVec
attribute [extern "lean_uint16_to_nat"] UInt16.toBitVec

/--
Pack a `Nat` less than `2^16` into a `UInt16`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint16_of_nat"]
def UInt16.ofNatLT (n : @& Nat) (h : LT.lt n UInt16.size) : UInt16 where
  toBitVec := BitVec.ofNatLT n h

set_option bootstrap.genMatcherCode false in
/--
Decides equality on `UInt16`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint16_dec_eq"]
def UInt16.decEq (a b : UInt16) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => UInt16.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt16 := UInt16.decEq

instance : Inhabited UInt16 where
  default := UInt16.ofNatLT 0 (of_decide_eq_true rfl)

/-- The size of type `UInt32`, that is, `2^32 = 4294967296`. -/
abbrev UInt32.size : Nat := 4294967296

/--
The type of unsigned 32-bit integers. This type has special support in the
compiler to make it actually 32 bits rather than wrapping a `Nat`.
-/
structure UInt32 where
  /--
  Create a `UInt32` from a `BitVec 32`. This function is overridden with a native implementation.
  -/
  ofBitVec ::
  /--
  Unpack a `UInt32` as a `BitVec 32`. This function is overridden with a native implementation.
  -/
  toBitVec : BitVec 32

attribute [extern "lean_uint32_of_nat_mk"] UInt32.ofBitVec
attribute [extern "lean_uint32_to_nat"] UInt32.toBitVec

/--
Pack a `Nat` less than `2^32` into a `UInt32`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint32_of_nat"]
def UInt32.ofNatLT (n : @& Nat) (h : LT.lt n UInt32.size) : UInt32 where
  toBitVec := BitVec.ofNatLT n h

/--
Unpack a `UInt32` as a `Nat`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint32_to_nat"]
def UInt32.toNat (n : UInt32) : Nat := n.toBitVec.toNat

set_option bootstrap.genMatcherCode false in
/--
Decides equality on `UInt32`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint32_dec_eq"]
def UInt32.decEq (a b : UInt32) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt32.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt32 := UInt32.decEq

instance : Inhabited UInt32 where
  default := UInt32.ofNatLT 0 (of_decide_eq_true rfl)

instance : LT UInt32 where
  lt a b := LT.lt a.toBitVec b.toBitVec

instance : LE UInt32 where
  le a b := LE.le a.toBitVec b.toBitVec

/--
Decides less-equal on `UInt32`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint32_dec_lt"]
def UInt32.decLt (a b : UInt32) : Decidable (LT.lt a b) :=
  inferInstanceAs (Decidable (LT.lt a.toBitVec b.toBitVec))

/--
Decides less-than on `UInt32`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint32_dec_le"]
def UInt32.decLe (a b : UInt32) : Decidable (LE.le a b) :=
  inferInstanceAs (Decidable (LE.le a.toBitVec b.toBitVec))

instance (a b : UInt32) : Decidable (LT.lt a b) := UInt32.decLt a b
instance (a b : UInt32) : Decidable (LE.le a b) := UInt32.decLe a b
instance : Max UInt32 := maxOfLe
instance : Min UInt32 := minOfLe

/-- The size of type `UInt64`, that is, `2^64 = 18446744073709551616`. -/
abbrev UInt64.size : Nat := 18446744073709551616
/--
The type of unsigned 64-bit integers. This type has special support in the
compiler to make it actually 64 bits rather than wrapping a `Nat`.
-/
structure UInt64 where
  /--
  Create a `UInt64` from a `BitVec 64`. This function is overridden with a native implementation.
  -/
  ofBitVec ::
  /--
  Unpack a `UInt64` as a `BitVec 64`. This function is overridden with a native implementation.
  -/
  toBitVec: BitVec 64

attribute [extern "lean_uint64_of_nat_mk"] UInt64.ofBitVec
attribute [extern "lean_uint64_to_nat"] UInt64.toBitVec

/--
Pack a `Nat` less than `2^64` into a `UInt64`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint64_of_nat"]
def UInt64.ofNatLT (n : @& Nat) (h : LT.lt n UInt64.size) : UInt64 where
  toBitVec := BitVec.ofNatLT n h

set_option bootstrap.genMatcherCode false in
/--
Decides equality on `UInt64`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint64_dec_eq"]
def UInt64.decEq (a b : UInt64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => UInt64.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt64 := UInt64.decEq

instance : Inhabited UInt64 where
  default := UInt64.ofNatLT 0 (of_decide_eq_true rfl)

/-- The size of type `USize`, that is, `2^System.Platform.numBits`. -/
abbrev USize.size : Nat := (hPow 2 System.Platform.numBits)

theorem USize.size_eq : Or (Eq USize.size 4294967296) (Eq USize.size 18446744073709551616) :=
  show Or (Eq (hPow 2 System.Platform.numBits) 4294967296) (Eq (hPow 2 System.Platform.numBits) 18446744073709551616) from
  match System.Platform.numBits, System.Platform.numBits_eq with
  | _, Or.inl rfl => Or.inl (of_decide_eq_true rfl)
  | _, Or.inr rfl => Or.inr (of_decide_eq_true rfl)

theorem USize.size_pos : LT.lt 0 USize.size :=
  match USize.size, USize.size_eq with
  | _, Or.inl rfl => of_decide_eq_true rfl
  | _, Or.inr rfl => of_decide_eq_true rfl

/--
A `USize` is an unsigned integer with the size of a word
for the platform's architecture.

For example, if running on a 32-bit machine, USize is equivalent to UInt32.
Or on a 64-bit machine, UInt64.
-/
structure USize where
  /--
  Create a `USize` from a `BitVec System.Platform.numBits`. This function is overridden with a
  native implementation.
  -/
  ofBitVec ::
  /--
  Unpack a `USize` as a `BitVec System.Platform.numBits`. This function is overridden with a native
  implementation.
  -/
  toBitVec : BitVec System.Platform.numBits

attribute [extern "lean_usize_of_nat_mk"] USize.ofBitVec
attribute [extern "lean_usize_to_nat"] USize.toBitVec

/--
Pack a `Nat` less than `USize.size` into a `USize`.
This function is overridden with a native implementation.
-/
@[extern "lean_usize_of_nat"]
def USize.ofNatLT (n : @& Nat) (h : LT.lt n USize.size) : USize where
  toBitVec := BitVec.ofNatLT n h

set_option bootstrap.genMatcherCode false in
/--
Decides equality on `USize`.
This function is overridden with a native implementation.
-/
@[extern "lean_usize_dec_eq"]
def USize.decEq (a b : USize) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => USize.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq USize := USize.decEq

instance : Inhabited USize where
  default := USize.ofNatLT 0 USize.size_pos

/--
A `Nat` denotes a valid unicode codepoint if it is less than `0x110000`, and
it is also not a "surrogate" character (the range `0xd800` to `0xdfff` inclusive).
-/
abbrev Nat.isValidChar (n : Nat) : Prop :=
  Or (LT.lt n 0xd800) (And (LT.lt 0xdfff n) (LT.lt n 0x110000))

/--
A `UInt32` denotes a valid unicode codepoint if it is less than `0x110000`, and
it is also not a "surrogate" character (the range `0xd800` to `0xdfff` inclusive).
-/
abbrev UInt32.isValidChar (n : UInt32) : Prop :=
  n.toNat.isValidChar

/-- The `Char` Type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure Char where
  /-- The underlying unicode scalar value as a `UInt32`. -/
  val   : UInt32
  /-- The value must be a legal codepoint. -/
  valid : val.isValidChar

private theorem isValidChar_UInt32 {n : Nat} (h : n.isValidChar) : LT.lt n UInt32.size :=
  match h with
  | Or.inl h      => Nat.lt_trans h (of_decide_eq_true rfl)
  | Or.inr ⟨_, h⟩ => Nat.lt_trans h (of_decide_eq_true rfl)

/--
Pack a `Nat` encoding a valid codepoint into a `Char`.
This function is overridden with a native implementation.
-/
@[extern "lean_uint32_of_nat"]
def Char.ofNatAux (n : @& Nat) (h : n.isValidChar) : Char :=
  { val := ⟨BitVec.ofNatLT n (isValidChar_UInt32 h)⟩, valid := h }

/--
Convert a `Nat` into a `Char`. If the `Nat` does not encode a valid unicode scalar value,
`'\0'` is returned instead.
-/
@[noinline, match_pattern]
def Char.ofNat (n : Nat) : Char :=
  dite (n.isValidChar)
    (fun h => Char.ofNatAux n h)
    (fun _ => { val := ⟨BitVec.ofNatLT 0 (of_decide_eq_true rfl)⟩, valid := Or.inl (of_decide_eq_true rfl) })

theorem Char.eq_of_val_eq : ∀ {c d : Char}, Eq c.val d.val → Eq c d
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Char.val_eq_of_eq : ∀ {c d : Char}, Eq c d → Eq c.val d.val
  | _, _, rfl => rfl

theorem Char.ne_of_val_ne {c d : Char} (h : Not (Eq c.val d.val)) : Not (Eq c d) :=
  fun h' => absurd (val_eq_of_eq h') h

theorem Char.val_ne_of_ne {c d : Char} (h : Not (Eq c d)) : Not (Eq c.val d.val) :=
  fun h' => absurd (eq_of_val_eq h') h

instance : DecidableEq Char :=
  fun c d =>
    match decEq c.val d.val with
    | isTrue h  => isTrue (Char.eq_of_val_eq h)
    | isFalse h => isFalse (Char.ne_of_val_ne h)

/-- Returns the number of bytes required to encode this `Char` in UTF-8. -/
def Char.utf8Size (c : Char) : Nat :=
  let v := c.val
  ite (LE.le v (UInt32.ofNatLT 0x7F (of_decide_eq_true rfl))) 1
    (ite (LE.le v (UInt32.ofNatLT 0x7FF (of_decide_eq_true rfl))) 2
      (ite (LE.le v (UInt32.ofNatLT 0xFFFF (of_decide_eq_true rfl))) 3 4))

/--
`Option α` is the type of values which are either `some a` for some `a : α`,
or `none`. In functional programming languages, this type is used to represent
the possibility of failure, or sometimes nullability.

For example, the function `HashMap.get? : HashMap α β → α → Option β` looks up
a specified key `a : α` inside the map. Because we do not know in advance
whether the key is actually in the map, the return type is `Option β`, where
`none` means the value was not in the map, and `some b` means that the value
was found and `b` is the value retrieved.

The `xs[i]` syntax, which is used to index into collections, has a variant
`xs[i]?` that returns an optional value depending on whether the given index
is valid. For example, if `m : HashMap α β` and `a : α`, then `m[a]?` is
equivalent to `HashMap.get? m a`.

To extract a value from an `Option α`, we use pattern matching:
```
def map (f : α → β) (x : Option α) : Option β :=
  match x with
  | some a => some (f a)
  | none => none
```
We can also use `if let` to pattern match on `Option` and get the value
in the branch:
```
def map (f : α → β) (x : Option α) : Option β :=
  if let some a := x then
    some (f a)
  else
    none
```
-/
inductive Option (α : Type u) where
  /-- No value. -/
  | none : Option α
  /-- Some value of type `α`. -/
  | some (val : α) : Option α

attribute [unbox] Option

export Option (none some)

instance {α} : Inhabited (Option α) where
  default := none

/--
Get with default. If `opt : Option α` and `dflt : α`, then `opt.getD dflt`
returns `a` if `opt = some a` and `dflt` otherwise.

This function is `@[macro_inline]`, so `dflt` will not be evaluated unless
`opt` turns out to be `none`.
-/
@[macro_inline] def Option.getD (opt : Option α) (dflt : α) : α :=
  match opt with
  | some x => x
  | none => dflt

/--
Map a function over an `Option` by applying the function to the contained
value if present.
-/
@[inline] protected def Option.map (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none   => none

/--
`List α` is the type of ordered lists with elements of type `α`.
It is implemented as a linked list.

`List α` is isomorphic to `Array α`, but they are useful for different things:
* `List α` is easier for reasoning, and
  `Array α` is modeled as a wrapper around `List α`
* `List α` works well as a persistent data structure, when many copies of the
  tail are shared. When the value is not shared, `Array α` will have better
  performance because it can do destructive updates.
-/
inductive List (α : Type u) where
  /-- `[]` is the empty list. -/
  | nil : List α
  /-- If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the
  list whose first element is `a` and with `l` as the rest of the list. -/
  | cons (head : α) (tail : List α) : List α

instance {α} : Inhabited (List α) where
  default := List.nil

/-- Implements decidable equality for `List α`, assuming `α` has decidable equality. -/
protected def List.hasDecEq {α : Type u} [DecidableEq α] : (a b : List α) → Decidable (Eq a b)
  | nil,       nil       => isTrue rfl
  | cons _ _, nil        => isFalse (fun h => List.noConfusion h)
  | nil,       cons _ _  => isFalse (fun h => List.noConfusion h)
  | cons a as, cons b bs =>
    match decEq a b with
    | isTrue hab  =>
      match List.hasDecEq as bs with
      | isTrue habs  => isTrue (hab ▸ habs ▸ rfl)
      | isFalse nabs => isFalse (fun h => List.noConfusion h (fun _ habs => absurd habs nabs))
    | isFalse nab => isFalse (fun h => List.noConfusion h (fun hab _ => absurd hab nab))

instance {α : Type u} [DecidableEq α] : DecidableEq (List α) := List.hasDecEq

/--
The length of a list: `[].length = 0` and `(a :: l).length = l.length + 1`.

This function is overridden in the compiler to `lengthTR`, which uses constant
stack space, while leaving this function to use the "naive" recursion which is
easier for reasoning.
-/
def List.length : List α → Nat
  | nil       => 0
  | cons _ as => HAdd.hAdd (length as) 1

/-- Auxiliary function for `List.lengthTR`. -/
def List.lengthTRAux : List α → Nat → Nat
  | nil,       n => n
  | cons _ as, n => lengthTRAux as (Nat.succ n)

/--
A tail-recursive version of `List.length`, used to implement `List.length`
without running out of stack space.
-/
def List.lengthTR (as : List α) : Nat :=
  lengthTRAux as 0

/--
`as.get i` returns the `i`'th element of the list `as`.
This version of the function uses `i : Fin as.length` to ensure that it will
not index out of bounds.
-/
def List.get {α : Type u} : (as : List α) → Fin as.length → α
  | cons a _,  ⟨0, _⟩ => a
  | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩

/--
`l.set n a` sets the value of list `l` at (zero-based) index `n` to `a`:
`[a, b, c, d].set 1 b' = [a, b', c, d]`
-/
def List.set : List α → Nat → α → List α
  | cons _ as, 0,          b => cons b as
  | cons a as, Nat.succ n, b => cons a (set as n b)
  | nil,       _,          _ => nil

/--
Folds a function over a list from the left:
`foldl f z [a, b, c] = f (f (f z a) b) c`
-/
@[specialize]
def List.foldl {α : Type u} {β : Type v} (f : α → β → α) : (init : α) → List β → α
  | a, nil      => a
  | a, cons b l => foldl f (f a b) l

/-- `l.concat a` appends `a` at the *end* of `l`, that is, `l ++ [a]`. -/
def List.concat {α : Type u} : List α → α → List α
  | nil,       b => cons b nil
  | cons a as, b => cons a (concat as b)

/--
`String` is the type of (UTF-8 encoded) strings.

The compiler overrides the data representation of this type to a byte sequence,
and both `String.utf8ByteSize` and `String.length` are cached and O(1).
-/
structure String where
  /-- Pack a `List Char` into a `String`. This function is overridden by the
  compiler and is O(n) in the length of the list. -/
  mk ::
  /-- Unpack `String` into a `List Char`. This function is overridden by the
  compiler and is O(n) in the length of the list. -/
  data : List Char

attribute [extern "lean_string_mk"] String.mk
attribute [extern "lean_string_data"] String.data

/--
Decides equality on `String`.
This function is overridden with a native implementation.
-/
@[extern "lean_string_dec_eq"]
def String.decEq (s₁ s₂ : @& String) : Decidable (Eq s₁ s₂) :=
  match s₁, s₂ with
  | ⟨s₁⟩, ⟨s₂⟩ =>
    dite (Eq s₁ s₂) (fun h => isTrue (congrArg _ h)) (fun h => isFalse (fun h' => String.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq String := String.decEq

/--
A byte position in a `String`. Internally, `String`s are UTF-8 encoded.
Codepoint positions (counting the Unicode codepoints rather than bytes)
are represented by plain `Nat`s instead.
Indexing a `String` by a byte position is constant-time, while codepoint
positions need to be translated internally to byte positions in linear-time.

A byte position `p` is *valid* for a string `s` if `0 ≤ p ≤ s.endPos` and `p`
lies on a UTF8 byte boundary.
-/
structure String.Pos where
  /-- Get the underlying byte index of a `String.Pos` -/
  byteIdx : Nat := 0

instance : Inhabited String.Pos where
  default := {}

instance : DecidableEq String.Pos :=
  fun ⟨a⟩ ⟨b⟩ => match decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun he => String.Pos.noConfusion he fun he => absurd he h)

/--
A `Substring` is a view into some subslice of a `String`.
The actual string slicing is deferred because this would require copying the
string; here we only store a reference to the original string for
garbage collection purposes.
-/
structure Substring where
  /-- The underlying string to slice. -/
  str      : String
  /-- The byte position of the start of the string slice. -/
  startPos : String.Pos
  /-- The byte position of the end of the string slice. -/
  stopPos  : String.Pos

instance : Inhabited Substring where
  default := ⟨"", {}, {}⟩

/-- The byte length of the substring. -/
@[inline] def Substring.bsize : Substring → Nat
  | ⟨_, b, e⟩ => e.byteIdx.sub b.byteIdx

/--
The UTF-8 byte length of this string.
This is overridden by the compiler to be cached and O(1).
-/
@[extern "lean_string_utf8_byte_size"]
def String.utf8ByteSize : (@& String) → Nat
  | ⟨s⟩ => go s
where
  go : List Char → Nat
   | .nil       => 0
   | .cons c cs => hAdd (go cs) c.utf8Size

instance : HAdd String.Pos String.Pos String.Pos where
  hAdd p₁ p₂ := { byteIdx := hAdd p₁.byteIdx p₂.byteIdx }

instance : HSub String.Pos String.Pos String.Pos where
  hSub p₁ p₂ := { byteIdx := HSub.hSub p₁.byteIdx p₂.byteIdx }

instance : HAdd String.Pos Char String.Pos where
  hAdd p c := { byteIdx := hAdd p.byteIdx c.utf8Size }

instance : HAdd String.Pos String String.Pos where
  hAdd p s := { byteIdx := hAdd p.byteIdx s.utf8ByteSize }

instance : LE String.Pos where
  le p₁ p₂ := LE.le p₁.byteIdx p₂.byteIdx

instance : LT String.Pos where
  lt p₁ p₂ := LT.lt p₁.byteIdx p₂.byteIdx

instance (p₁ p₂ : String.Pos) : Decidable (LE.le p₁ p₂) :=
  inferInstanceAs (Decidable (LE.le p₁.byteIdx p₂.byteIdx))

instance (p₁ p₂ : String.Pos) : Decidable (LT.lt p₁ p₂) :=
  inferInstanceAs (Decidable (LT.lt p₁.byteIdx p₂.byteIdx))

instance : Min String.Pos := minOfLe
instance : Max String.Pos := maxOfLe

/-- A `String.Pos` pointing at the end of this string. -/
@[inline] def String.endPos (s : String) : String.Pos where
  byteIdx := utf8ByteSize s

/-- Convert a `String` into a `Substring` denoting the entire string. -/
@[inline] def String.toSubstring (s : String) : Substring where
  str      := s
  startPos := {}
  stopPos  := s.endPos

/-- `String.toSubstring` without `[inline]` annotation. -/
def String.toSubstring' (s : String) : Substring :=
  s.toSubstring

/--
This function will cast a value of type `α` to type `β`, and is a no-op in the
compiler. This function is **extremely dangerous** because there is no guarantee
that types `α` and `β` have the same data representation, and this can lead to
memory unsafety. It is also logically unsound, since you could just cast
`True` to `False`. For all those reasons this function is marked as `unsafe`.

It is implemented by lifting both `α` and `β` into a common universe, and then
using `cast (lcProof : ULift (PLift α) = ULift (PLift β))` to actually perform
the cast. All these operations are no-ops in the compiler.

Using this function correctly requires some knowledge of the data representation
of the source and target types. Some general classes of casts which are safe in
the current runtime:

* `Array α` to `Array β` where `α` and `β` have compatible representations,
  or more generally for other inductive types.
* `Quot α r` and `α`.
* `@Subtype α p` and `α`, or generally any structure containing only one
  non-`Prop` field of type `α`.
* Casting `α` to/from `NonScalar` when `α` is a boxed generic type
  (i.e. a function that accepts an arbitrary type `α` and is not specialized to
  a scalar type like `UInt8`).
-/
unsafe def unsafeCast {α : Sort u} {β : Sort v} (a : α) : β :=
  PLift.down (ULift.down.{max u v} (cast lcProof (ULift.up.{max u v} (PLift.up a))))


/-- Auxiliary definition for `panic`. -/
/-
This is a workaround for `panic` occurring in monadic code. See issue #695.
The `panicCore` definition cannot be specialized since it is an extern.
When `panic` occurs in monadic code, the `Inhabited α` parameter depends on a
`[inst : Monad m]` instance. The `inst` parameter will not be eliminated during
specialization if it occurs inside of a binder (to avoid work duplication), and
will prevent the actual monad from being "copied" to the code being specialized.
When we reimplement the specializer, we may consider copying `inst` if it also
occurs outside binders or if it is an instance.
-/
@[never_extract, extern "lean_panic_fn"]
def panicCore {α : Sort u} [Inhabited α] (msg : String) : α := default

/--
`(panic "msg" : α)` has a built-in implementation which prints `msg` to
the error buffer. It *does not* terminate execution, and because it is a safe
function, it still has to return an element of `α`, so it takes `[Inhabited α]`
and returns `default`. It is primarily intended for debugging in pure contexts,
and assertion failures.

Because this is a pure function with side effects, it is marked as
`@[never_extract]` so that the compiler will not perform common sub-expression
elimination and other optimizations that assume that the expression is pure.
-/
@[noinline, never_extract]
def panic {α : Sort u} [Inhabited α] (msg : String) : α :=
  panicCore msg

-- TODO: this be applied directly to `Inhabited`'s definition when we remove the above workaround
attribute [nospecialize] Inhabited

/--
`Array α` is the type of [dynamic arrays](https://en.wikipedia.org/wiki/Dynamic_array)
with elements from `α`. This type has special support in the runtime.

An array has a size and a capacity; the size is `Array.size` but the capacity
is not observable from Lean code. Arrays perform best when unshared; as long
as they are used "linearly" all updates will be performed destructively on the
array, so it has comparable performance to mutable arrays in imperative
programming languages.

From the point of view of proofs `Array α` is just a wrapper around `List α`.
-/
structure Array (α : Type u) where
  /--
  Converts a `List α` into an `Array α`.

  You can also use the synonym `List.toArray` when dot notation is convenient.

  At runtime, this constructor is implemented by `List.toArrayImpl` and is O(n) in the length of the
  list.
  -/
  mk ::
  /--
  Converts a `Array α` into an `List α`.

  At runtime, this projection is implemented by `Array.toListImpl` and is O(n) in the length of the
  array. -/
  toList : List α

attribute [extern "lean_array_to_list"] Array.toList
attribute [extern "lean_array_mk"] Array.mk

/--
Converts a `List α` into an `Array α`. (This is preferred over the synonym `Array.mk`.)

At runtime, this constructor is implemented by `List.toArrayImpl` and is O(n) in the length of the
list.
-/
@[match_pattern]
abbrev List.toArray (xs : List α) : Array α := .mk xs

/-- Construct a new empty array with initial capacity `c`. -/
@[extern "lean_mk_empty_array_with_capacity"]
def Array.mkEmpty {α : Type u} (c : @& Nat) : Array α where
  toList := List.nil

/-- Construct a new empty array. -/
def Array.empty {α : Type u} : Array α := mkEmpty 0

/-- Get the size of an array. This is a cached value, so it is O(1) to access. -/
@[reducible, extern "lean_array_get_size"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
 a.toList.length

/--
Use the indexing notation `a[i]` instead.

Access an element from an array without needing a runtime bounds checks,
using a `Nat` index and a proof that it is in bounds.

This function does not use `get_elem_tactic` to automatically find the proof that
the index is in bounds. This is because the tactic itself needs to look up values in
arrays.
-/
@[extern "lean_array_fget"]
def Array.getInternal {α : Type u} (a : @& Array α) (i : @& Nat) (h : LT.lt i a.size) : α :=
  a.toList.get ⟨i, h⟩

/-- Access an element from an array, or return `v₀` if the index is out of bounds. -/
@[inline] abbrev Array.getD (a : Array α) (i : Nat) (v₀ : α) : α :=
  dite (LT.lt i a.size) (fun h => a.getInternal i h) (fun _ => v₀)

/--
Use the indexing notation `a[i]!` instead.

Access an element from an array, or panic if the index is out of bounds.
-/
@[extern "lean_array_get"]
def Array.get!Internal {α : Type u} [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
  Array.getD a i default

/--
Push an element onto the end of an array. This is amortized O(1) because
`Array α` is internally a dynamic array.
-/
@[extern "lean_array_push"]
def Array.push {α : Type u} (a : Array α) (v : α) : Array α where
  toList := List.concat a.toList v

/-- Create array `#[]` -/
def Array.mkArray0 {α : Type u} : Array α :=
  mkEmpty 0

/-- Create array `#[a₁]` -/
def Array.mkArray1 {α : Type u} (a₁ : α) : Array α :=
  (mkEmpty 1).push a₁

/-- Create array `#[a₁, a₂]` -/
def Array.mkArray2 {α : Type u} (a₁ a₂ : α) : Array α :=
  ((mkEmpty 2).push a₁).push a₂

/-- Create array `#[a₁, a₂, a₃]` -/
def Array.mkArray3 {α : Type u} (a₁ a₂ a₃ : α) : Array α :=
  (((mkEmpty 3).push a₁).push a₂).push a₃

/-- Create array `#[a₁, a₂, a₃, a₄]` -/
def Array.mkArray4 {α : Type u} (a₁ a₂ a₃ a₄ : α) : Array α :=
  ((((mkEmpty 4).push a₁).push a₂).push a₃).push a₄

/-- Create array `#[a₁, a₂, a₃, a₄, a₅]` -/
def Array.mkArray5 {α : Type u} (a₁ a₂ a₃ a₄ a₅ : α) : Array α :=
  (((((mkEmpty 5).push a₁).push a₂).push a₃).push a₄).push a₅

/-- Create array `#[a₁, a₂, a₃, a₄, a₅, a₆]` -/
def Array.mkArray6 {α : Type u} (a₁ a₂ a₃ a₄ a₅ a₆ : α) : Array α :=
  ((((((mkEmpty 6).push a₁).push a₂).push a₃).push a₄).push a₅).push a₆

/-- Create array `#[a₁, a₂, a₃, a₄, a₅, a₆, a₇]` -/
def Array.mkArray7 {α : Type u} (a₁ a₂ a₃ a₄ a₅ a₆ a₇ : α) : Array α :=
  (((((((mkEmpty 7).push a₁).push a₂).push a₃).push a₄).push a₅).push a₆).push a₇

/-- Create array `#[a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈]` -/
def Array.mkArray8 {α : Type u} (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : α) : Array α :=
  ((((((((mkEmpty 8).push a₁).push a₂).push a₃).push a₄).push a₅).push a₆).push a₇).push a₈

/-- Slower `Array.append` used in quotations. -/
protected def Array.appendCore {α : Type u}  (as : Array α) (bs : Array α) : Array α :=
  let rec loop (i : Nat) (j : Nat) (as : Array α) : Array α :=
    dite (LT.lt j bs.size)
      (fun hlt =>
        match i with
        | 0           => as
        | Nat.succ i' => loop i' (hAdd j 1) (as.push (bs.getInternal j hlt)))
      (fun _ => as)
  loop bs.size 0 as

/--
  Returns the slice of `as` from indices `start` to `stop` (exclusive).
  If `start` is greater or equal to `stop`, the result is empty.
  If `stop` is greater than the length of `as`, the length is used instead. -/
-- NOTE: used in the quotation elaborator output
def Array.extract (as : Array α) (start : Nat := 0) (stop : Nat := as.size) : Array α :=
  let rec loop (i : Nat) (j : Nat) (bs : Array α) : Array α :=
    dite (LT.lt j as.size)
      (fun hlt =>
        match i with
        | 0           => bs
        | Nat.succ i' => loop i' (hAdd j 1) (bs.push (as.getInternal j hlt)))
      (fun _ => bs)
  let sz' := Nat.sub (min stop as.size) start
  loop sz' start (mkEmpty sz')

/-- The typeclass which supplies the `>>=` "bind" function. See `Monad`. -/
class Bind (m : Type u → Type v) where
  /-- If `x : m α` and `f : α → m β`, then `x >>= f : m β` represents the
  result of executing `x` to get a value of type `α` and then passing it to `f`. -/
  bind : {α β : Type u} → m α → (α → m β) → m β

export Bind (bind)

/-- The typeclass which supplies the `pure` function. See `Monad`. -/
class Pure (f : Type u → Type v) where
  /-- If `a : α`, then `pure a : f α` represents a monadic action that does
  nothing and returns `a`. -/
  pure {α : Type u} : α → f α

export Pure (pure)

/--
In functional programming, a "functor" is a function on types `F : Type u → Type v`
equipped with an operator called `map` or `<$>` such that if `f : α → β` then
`map f : F α → F β`, so `f <$> x : F β` if `x : F α`. This corresponds to the
category-theory notion of [functor](https://en.wikipedia.org/wiki/Functor) in
the special case where the category is the category of types and functions
between them, except that this class supplies only the operations and not the
laws (see `LawfulFunctor`).
-/
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  /-- If `f : α → β` and `x : F α` then `f <$> x : F β`. -/
  map : {α β : Type u} → (α → β) → f α → f β
  /-- The special case `const a <$> x`, which can sometimes be implemented more
  efficiently. -/
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)

/-- The typeclass which supplies the `<*>` "seq" function. See `Applicative`. -/
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  /-- If `mf : F (α → β)` and `mx : F α`, then `mf <*> mx : F β`.
  In a monad this is the same as `do let f ← mf; x ← mx; pure (f x)`:
  it evaluates first the function, then the argument, and applies one to the other.

  To avoid surprising evaluation semantics, `mx` is taken "lazily", using a
  `Unit → f α` function. -/
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

/-- The typeclass which supplies the `<*` "seqLeft" function. See `Applicative`. -/
class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  /-- If `x : F α` and `y : F β`, then `x <* y` evaluates `x`, then `y`,
  and returns the result of `x`.

  To avoid surprising evaluation semantics, `y` is taken "lazily", using a
  `Unit → f β` function. -/
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

/-- The typeclass which supplies the `*>` "seqRight" function. See `Applicative`. -/
class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  /-- If `x : F α` and `y : F β`, then `x *> y` evaluates `x`, then `y`,
  and returns the result of `y`.

  To avoid surprising evaluation semantics, `y` is taken "lazily", using a
  `Unit → f β` function. -/
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β

/--
An [applicative functor](https://en.wikipedia.org/wiki/Applicative_functor) is
an intermediate structure between `Functor` and `Monad`. It mainly consists of
two operations:

* `pure : α → F α`
* `seq : F (α → β) → F α → F β` (written as `<*>`)

The `seq` operator gives a notion of evaluation order to the effects, where
the first argument is executed before the second, but unlike a monad the results
of earlier computations cannot be used to define later actions.
-/
class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b

/--
A [monad](https://en.wikipedia.org/wiki/Monad_(functional_programming)) is a
structure which abstracts the concept of sequential control flow.
It mainly consists of two operations:

* `pure : α → F α`
* `bind : F α → (α → F β) → F β` (written as `>>=`)

Like many functional programming languages, Lean makes extensive use of monads
for structuring programs. In particular, the `do` notation is a very powerful
syntax over monad operations, and it depends on a `Monad` instance.

See [the `do` notation](https://lean-lang.org/lean4/doc/do.html)
chapter of the manual for details.
-/
class Monad (m : Type u → Type v) : Type (max (u+1) v) extends Applicative m, Bind m where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()

instance {α : Type u} {m : Type u → Type v} [Monad m] : Inhabited (α → m α) where
  default := pure

instance {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] : Inhabited (m α) where
  default := pure default

instance [Monad m] : [Nonempty α] → Nonempty (m α)
  | ⟨x⟩ => ⟨pure x⟩

/--
A function for lifting a computation from an inner `Monad` to an outer `Monad`.
Like Haskell's [`MonadTrans`], but `n` does not have to be a monad transformer.
Alternatively, an implementation of [`MonadLayer`] without `layerInvmap` (so far).

  [`MonadTrans`]: https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html
  [`MonadLayer`]: https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer
-/
class MonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  /-- Lifts a value from monad `m` into monad `n`. -/
  monadLift : {α : Type u} → m α → n α

/--
The reflexive-transitive closure of `MonadLift`. `monadLift` is used to
transitively lift monadic computations such as `StateT.get` or `StateT.put s`.
Corresponds to Haskell's [`MonadLift`].

  [`MonadLift`]: https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift
-/
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) where
  /-- Lifts a value from monad `m` into monad `n`. -/
  monadLift : {α : Type u} → m α → n α

export MonadLiftT (monadLift)

/-- Lifts a value from monad `m` into monad `n`. -/
abbrev liftM := @monadLift

@[always_inline]
instance (m n o) [MonadLift n o] [MonadLiftT m n] : MonadLiftT m o where
  monadLift x := MonadLift.monadLift (m := n) (monadLift x)

instance (m) : MonadLiftT m m where
  monadLift x := x

/--
Typeclass used for adapting monads. This is similar to `MonadLift`, but instances are allowed to
make use of default state for the purpose of synthesizing such an instance, if necessary.
Every `MonadLift` instance gives a `MonadEval` instance.

The purpose of this class is for the `#eval` command,
which looks for a `MonadEval m CommandElabM` or `MonadEval m IO` instance.
-/
class MonadEval (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  /-- Evaluates a value from monad `m` into monad `n`. -/
  monadEval : {α : Type u} → m α → n α

instance [MonadLift m n] : MonadEval m n where
  monadEval := MonadLift.monadLift

/-- The transitive closure of `MonadEval`. -/
class MonadEvalT (m : Type u → Type v) (n : Type u → Type w) where
  /-- Evaluates a value from monad `m` into monad `n`. -/
  monadEval : {α : Type u} → m α → n α

instance (m n o) [MonadEval n o] [MonadEvalT m n] : MonadEvalT m o where
  monadEval x := MonadEval.monadEval (m := n) (MonadEvalT.monadEval x)

instance (m) : MonadEvalT m m where
  monadEval x := x

/--
A functor in the category of monads. Can be used to lift monad-transforming functions.
Based on [`MFunctor`] from the `pipes` Haskell package, but not restricted to
monad transformers. Alternatively, an implementation of [`MonadTransFunctor`].

  [`MFunctor`]: https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html
  [`MonadTransFunctor`]: http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor
-/
class MonadFunctor (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  /-- Lifts a monad morphism `f : {β : Type u} → m β → m β` to
  `monadMap f : {α : Type u} → n α → n α`. -/
  monadMap {α : Type u} : ({β : Type u} → m β → m β) → n α → n α

/-- The reflexive-transitive closure of `MonadFunctor`.
`monadMap` is used to transitively lift `Monad` morphisms. -/
class MonadFunctorT (m : Type u → Type v) (n : Type u → Type w) where
  /-- Lifts a monad morphism `f : {β : Type u} → m β → m β` to
  `monadMap f : {α : Type u} → n α → n α`. -/
  monadMap {α : Type u} : ({β : Type u} → m β → m β) → n α → n α

export MonadFunctorT (monadMap)

@[always_inline]
instance (m n o) [MonadFunctor n o] [MonadFunctorT m n] : MonadFunctorT m o where
  monadMap f := MonadFunctor.monadMap (m := n) (monadMap (m := m) f)

instance monadFunctorRefl (m) : MonadFunctorT m m where
  monadMap f := f

/--
`Except ε α` is a type which represents either an error of type `ε`, or an "ok"
value of type `α`. The error type is listed first because
`Except ε : Type → Type` is a `Monad`: the pure operation is `ok` and the bind
operation returns the first encountered `error`.
-/
inductive Except (ε : Type u) (α : Type v) where
  /-- A failure value of type `ε` -/
  | error : ε → Except ε α
  /-- A success value of type `α` -/
  | ok    : α → Except ε α

attribute [unbox] Except

instance {ε : Type u} {α : Type v} [Inhabited ε] : Inhabited (Except ε α) where
  default := Except.error default

/--
An implementation of Haskell's [`MonadError`] class. A `MonadError ε m` is a
monad `m` with two operations:

* `throw : ε → m α` "throws an error" of type `ε` to the nearest enclosing
  catch block
* `tryCatch (body : m α) (handler : ε → m α) : m α` will catch any errors in
  `body` and pass the resulting error to `handler`.
  Errors in `handler` will not be caught.

The `try ... catch e => ...` syntax inside `do` blocks is sugar for the
`tryCatch` operation.

  [`MonadError`]: https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError
-/
class MonadExceptOf (ε : semiOutParam (Type u)) (m : Type v → Type w) where
  /-- `throw : ε → m α` "throws an error" of type `ε` to the nearest enclosing
  catch block. -/
  throw {α : Type v} : ε → m α
  /-- `tryCatch (body : m α) (handler : ε → m α) : m α` will catch any errors in
  `body` and pass the resulting error to `handler`.
  Errors in `handler` will not be caught. -/
  tryCatch {α : Type v} (body : m α) (handler : ε → m α) : m α

/--
This is the same as `throw`, but allows specifying the particular error type
in case the monad supports throwing more than one type of error.
-/
abbrev throwThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (e : ε) : m α :=
  MonadExceptOf.throw e

/--
This is the same as `tryCatch`, but allows specifying the particular error type
in case the monad supports throwing more than one type of error.
-/
abbrev tryCatchThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (x : m α) (handle : ε → m α) : m α :=
  MonadExceptOf.tryCatch x handle

/-- Similar to `MonadExceptOf`, but `ε` is an `outParam` for convenience. -/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  /-- `throw : ε → m α` "throws an error" of type `ε` to the nearest enclosing
  catch block. -/
  throw {α : Type v} : ε → m α
  /-- `tryCatch (body : m α) (handler : ε → m α) : m α` will catch any errors in
  `body` and pass the resulting error to `handler`.
  Errors in `handler` will not be caught. -/
  tryCatch {α : Type v} : m α → (ε → m α) → m α

/-- "Unwraps" an `Except ε α` to get the `α`, or throws the exception otherwise. -/
def MonadExcept.ofExcept [Monad m] [MonadExcept ε m] : Except ε α → m α
  | .ok a    => pure a
  | .error e => throw e

export MonadExcept (throw tryCatch ofExcept)

instance (ε : Type u) (m : Type v → Type w) [MonadExceptOf ε m] : MonadExcept ε m where
  throw    := throwThe ε
  tryCatch := tryCatchThe ε

namespace MonadExcept
variable {ε : Type u} {m : Type v → Type w}

/-- A `MonadExcept` can implement `t₁ <|> t₂` as `try t₁ catch _ => t₂`. -/
@[inline] protected def orElse [MonadExcept ε m] {α : Type v} (t₁ : m α) (t₂ : Unit → m α) : m α :=
  tryCatch t₁ fun _ => t₂ ()

instance [MonadExcept ε m] {α : Type v} : OrElse (m α) where
  orElse := MonadExcept.orElse

end MonadExcept

/--
An implementation of Haskell's [`ReaderT`]. This is a monad transformer which
equips a monad with additional read-only state, of type `ρ`.

  [`ReaderT`]: https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT
-/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α

instance (ρ : Type u) (m : Type u → Type v) (α : Type u) [Inhabited (m α)] : Inhabited (ReaderT ρ m α) where
  default := fun _ => default

/--
If `x : ReaderT ρ m α` and `r : ρ`, then `x.run r : ρ` runs the monad with the
given reader state.
-/
@[always_inline, inline]
def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
  x r

namespace ReaderT

section
variable {ρ : Type u} {m : Type u → Type v} {α : Type u}

instance  : MonadLift m (ReaderT ρ m) where
  monadLift x := fun _ => x

@[always_inline]
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ReaderT ρ m) where
  throw e  := liftM (m := m) (throw e)
  tryCatch := fun x c r => tryCatchThe ε (x r) (fun e => (c e) r)

end

section
variable {ρ : Type u} {m : Type u → Type v}

/-- `(← read) : ρ` gets the read-only state of a `ReaderT ρ`. -/
@[always_inline, inline]
protected def read [Monad m] : ReaderT ρ m ρ :=
  pure

/-- The `pure` operation of the `ReaderT` monad. -/
@[always_inline, inline]
protected def pure [Monad m] {α} (a : α) : ReaderT ρ m α :=
  fun _ => pure a

/-- The `bind` operation of the `ReaderT` monad. -/
@[always_inline, inline]
protected def bind [Monad m] {α β} (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) : ReaderT ρ m β :=
  fun r => bind (x r) fun a => f a r

@[always_inline]
instance [Monad m] : Functor (ReaderT ρ m) where
  map      f x r := Functor.map f (x r)
  mapConst a x r := Functor.mapConst a (x r)

@[always_inline]
instance [Monad m] : Applicative (ReaderT ρ m) where
  pure           := ReaderT.pure
  seq      f x r := Seq.seq (f r) fun _ => x () r
  seqLeft  a b r := SeqLeft.seqLeft (a r) fun _ => b () r
  seqRight a b r := SeqRight.seqRight (a r) fun _ => b () r

instance [Monad m] : Monad (ReaderT ρ m) where
  bind := ReaderT.bind

instance (ρ m) : MonadFunctor m (ReaderT ρ m) where
  monadMap f x := fun ctx => f (x ctx)

/--
`adapt (f : ρ' → ρ)` precomposes function `f` on the reader state of a
`ReaderT ρ`, yielding a `ReaderT ρ'`.
-/
@[always_inline, inline]
protected def adapt {ρ' α : Type u} (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α :=
  fun x r => x (f r)

end
end ReaderT

/--
An implementation of Haskell's [`MonadReader`] (sans functional dependency; see also `MonadReader`
in this module). It does not contain `local` because this
function cannot be lifted using `monadLift`. `local` is instead provided by
the `MonadWithReader` class as `withReader`.

Note: This class can be seen as a simplification of the more "principled" definition
```
class MonadReaderOf (ρ : Type u) (n : Type u → Type u) where
  lift {α : Type u} : ({m : Type u → Type u} → [Monad m] → ReaderT ρ m α) → n α
```

  [`MonadReader`]: https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader
-/
class MonadReaderOf (ρ : semiOutParam (Type u)) (m : Type u → Type v) where
  /-- `(← read) : ρ` reads the state out of monad `m`. -/
  read : m ρ

/--
Like `read`, but with `ρ` explicit. This is useful if a monad supports
`MonadReaderOf` for multiple different types `ρ`.
-/
@[always_inline, inline]
def readThe (ρ : Type u) {m : Type u → Type v} [MonadReaderOf ρ m] : m ρ :=
  MonadReaderOf.read

/-- Similar to `MonadReaderOf`, but `ρ` is an `outParam` for convenience. -/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  /-- `(← read) : ρ` reads the state out of monad `m`. -/
  read : m ρ

export MonadReader (read)

instance (ρ : Type u) (m : Type u → Type v) [MonadReaderOf ρ m] : MonadReader ρ m where
  read := readThe ρ

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n] [MonadReaderOf ρ m] : MonadReaderOf ρ n where
  read := liftM (m := m) read

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadReaderOf ρ (ReaderT ρ m) where
  read := ReaderT.read

/--
`MonadWithReaderOf ρ` adds the operation `withReader : (ρ → ρ) → m α → m α`.
This runs the inner `x : m α` inside a modified context after applying the
function `f : ρ → ρ`. In addition to `ReaderT` itself, this operation lifts
over most monad transformers, so it allows us to apply `withReader` to monads
deeper in the stack.
-/
class MonadWithReaderOf (ρ : semiOutParam (Type u)) (m : Type u → Type v) where
  /-- `withReader (f : ρ → ρ) (x : m α) : m α`  runs the inner `x : m α` inside
  a modified context after applying the function `f : ρ → ρ`.-/
  withReader {α : Type u} : (ρ → ρ) → m α → m α

/--
Like `withReader`, but with `ρ` explicit. This is useful if a monad supports
`MonadWithReaderOf` for multiple different types `ρ`.
-/
@[always_inline, inline]
def withTheReader (ρ : Type u) {m : Type u → Type v} [MonadWithReaderOf ρ m] {α : Type u} (f : ρ → ρ) (x : m α) : m α :=
  MonadWithReaderOf.withReader f x

/-- Similar to `MonadWithReaderOf`, but `ρ` is an `outParam` for convenience. -/
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  /-- `withReader (f : ρ → ρ) (x : m α) : m α`  runs the inner `x : m α` inside
  a modified context after applying the function `f : ρ → ρ`.-/
  withReader {α : Type u} : (ρ → ρ) → m α → m α

export MonadWithReader (withReader)

instance (ρ : Type u) (m : Type u → Type v) [MonadWithReaderOf ρ m] : MonadWithReader ρ m where
  withReader := withTheReader ρ

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type v} [MonadFunctor m n] [MonadWithReaderOf ρ m] : MonadWithReaderOf ρ n where
  withReader f := monadMap (m := m) (withTheReader ρ f)

instance {ρ : Type u} {m : Type u → Type v} : MonadWithReaderOf ρ (ReaderT ρ m) where
  withReader f x := fun ctx => x (f ctx)

/--
An implementation of [`MonadState`]. In contrast to the Haskell implementation,
we use overlapping instances to derive instances automatically from `monadLift`.

  [`MonadState`]: https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html
-/
class MonadStateOf (σ : semiOutParam (Type u)) (m : Type u → Type v) where
  /-- `(← get) : σ` gets the state out of a monad `m`. -/
  get : m σ
  /-- `set (s : σ)` replaces the state with value `s`. -/
  set : σ → m PUnit
  /-- `modifyGet (f : σ → α × σ)` applies `f` to the current state, replaces
  the state with the return value, and returns a computed value.

  It is equivalent to `do let (a, s) := f (← get); put s; pure a`, but
  `modifyGet f` may be preferable because the former does not use the state
  linearly (without sufficient inlining). -/
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

export MonadStateOf (set)

/--
Like `get`, but with `σ` explicit. This is useful if a monad supports
`MonadStateOf` for multiple different types `σ`.
-/
abbrev getThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] : m σ :=
  MonadStateOf.get

/--
Like `modify`, but with `σ` explicit. This is useful if a monad supports
`MonadStateOf` for multiple different types `σ`.
-/
@[always_inline, inline]
abbrev modifyThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → σ) : m PUnit :=
  MonadStateOf.modifyGet fun s => (PUnit.unit, f s)

/--
Like `modifyGet`, but with `σ` explicit. This is useful if a monad supports
`MonadStateOf` for multiple different types `σ`.
-/
@[always_inline, inline]
abbrev modifyGetThe {α : Type u} (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → Prod α σ) : m α :=
  MonadStateOf.modifyGet f

/-- Similar to `MonadStateOf`, but `σ` is an `outParam` for convenience. -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) where
  /-- `(← get) : σ` gets the state out of a monad `m`. -/
  get : m σ
  /-- `set (s : σ)` replaces the state with value `s`. -/
  set : σ → m PUnit
  /-- `modifyGet (f : σ → α × σ)` applies `f` to the current state, replaces
  the state with the return value, and returns a computed value.

  It is equivalent to `do let (a, s) := f (← get); put s; pure a`, but
  `modifyGet f` may be preferable because the former does not use the state
  linearly (without sufficient inlining). -/
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

export MonadState (get modifyGet)

instance (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] : MonadState σ m where
  set         := MonadStateOf.set
  get         := getThe σ
  modifyGet f := MonadStateOf.modifyGet f

/--
`modify (f : σ → σ)` applies the function `f` to the state.

It is equivalent to `do set (f (← get))`, but `modify f` may be preferable
because the former does not use the state linearly (without sufficient inlining).
-/
@[always_inline, inline]
def modify {σ : Type u} {m : Type u → Type v} [MonadState σ m] (f : σ → σ) : m PUnit :=
  modifyGet fun s => (PUnit.unit, f s)

/--
`getModify f` gets the state, applies function `f`, and returns the old value
of the state. It is equivalent to `get <* modify f` but may be more efficient.
-/
@[always_inline, inline]
def getModify {σ : Type u} {m : Type u → Type v} [MonadState σ m] (f : σ → σ) : m σ :=
  modifyGet fun s => (s, f s)

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
@[always_inline]
instance {σ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n] [MonadStateOf σ m] : MonadStateOf σ n where
  get         := liftM (m := m) MonadStateOf.get
  set       s := liftM (m := m) (MonadStateOf.set s)
  modifyGet f := monadLift (m := m) (MonadState.modifyGet f)

namespace EStateM

/--
`Result ε σ α` is equivalent to `Except ε α × σ`, but using a single
combined inductive yields a more efficient data representation.
-/
inductive Result (ε σ α : Type u) where
  /-- A success value of type `α`, and a new state `σ`. -/
  | ok    : α → σ → Result ε σ α
  /-- A failure value of type `ε`, and a new state `σ`. -/
  | error : ε → σ → Result ε σ α

variable {ε σ α : Type u}

instance [Inhabited ε] [Inhabited σ] : Inhabited (Result ε σ α) where
  default := Result.error default default

end EStateM

open EStateM (Result) in
/--
`EStateM ε σ` is a combined error and state monad, equivalent to
`ExceptT ε (StateM σ)` but more efficient.
-/
def EStateM (ε σ α : Type u) := σ → Result ε σ α

namespace EStateM

variable {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EStateM ε σ α) where
  default := fun s => Result.error default s

/-- The `pure` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def pure (a : α) : EStateM ε σ α := fun s =>
  Result.ok a s

/-- The `set` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def set (s : σ) : EStateM ε σ PUnit := fun _ =>
  Result.ok ⟨⟩ s

/-- The `get` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def get : EStateM ε σ σ := fun s =>
  Result.ok s s

/-- The `modifyGet` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def modifyGet (f : σ → Prod α σ) : EStateM ε σ α := fun s =>
  match f s with
  | (a, s) => Result.ok a s

/-- The `throw` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def throw (e : ε) : EStateM ε σ α := fun s =>
  Result.error e s

/--
Auxiliary instance for saving/restoring the "backtrackable" part of the state.
Here `σ` is the state, and `δ` is some subpart of it, and we have a
getter and setter for it (a "lens" in the Haskell terminology).
-/
class Backtrackable (δ : outParam (Type u)) (σ : Type u) where
  /-- `save s : δ` retrieves a copy of the backtracking state out of the state. -/
  save    : σ → δ
  /-- `restore (s : σ) (x : δ) : σ` applies the old backtracking state `x` to
  the state `s` to get a backtracked state `s'`. -/
  restore : σ → δ → σ

/-- Implementation of `tryCatch` for `EStateM` where the state is `Backtrackable`. -/
@[always_inline, inline]
protected def tryCatch {δ} [Backtrackable δ σ] {α} (x : EStateM ε σ α) (handle : ε → EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s
  match x s with
  | Result.error e s => handle e (Backtrackable.restore s d)
  | ok               => ok

/-- Implementation of `orElse` for `EStateM` where the state is `Backtrackable`. -/
@[always_inline, inline]
protected def orElse {δ} [Backtrackable δ σ] (x₁ : EStateM ε σ α) (x₂ : Unit → EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error _ s => x₂ () (Backtrackable.restore s d)
  | ok               => ok

/-- Map the exception type of a `EStateM ε σ α` by a function `f : ε → ε'`. -/
@[always_inline, inline]
def adaptExcept {ε' : Type u} (f : ε → ε') (x : EStateM ε σ α) : EStateM ε' σ α := fun s =>
  match x s with
  | Result.error e s => Result.error (f e) s
  | Result.ok a s    => Result.ok a s

/-- The `bind` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => f a s
  | Result.error e s => Result.error e s

/-- The `map` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def map (f : α → β) (x : EStateM ε σ α) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

/-- The `seqRight` operation of the `EStateM` monad. -/
@[always_inline, inline]
protected def seqRight (x : EStateM ε σ α) (y : Unit → EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok _ s    => y () s
  | Result.error e s => Result.error e s

@[always_inline]
instance instMonad : Monad (EStateM ε σ) where
  bind     := EStateM.bind
  pure     := EStateM.pure
  map      := EStateM.map
  seqRight := EStateM.seqRight

instance {δ} [Backtrackable δ σ] : OrElse (EStateM ε σ α) where
  orElse := EStateM.orElse

instance : MonadStateOf σ (EStateM ε σ) where
  set       := EStateM.set
  get       := EStateM.get
  modifyGet := EStateM.modifyGet

instance {δ} [Backtrackable δ σ] : MonadExceptOf ε (EStateM ε σ) where
  throw    := EStateM.throw
  tryCatch := EStateM.tryCatch

/-- Execute an `EStateM` on initial state `s` to get a `Result`. -/
@[always_inline, inline]
def run (x : EStateM ε σ α) (s : σ) : Result ε σ α := x s

/--
Execute an `EStateM` on initial state `s` for the returned value `α`.
If the monadic action throws an exception, returns `none` instead.
-/
@[always_inline, inline]
def run' (x : EStateM ε σ α) (s : σ) : Option α :=
  match run x s with
  | Result.ok v _   => some v
  | Result.error .. => none

/-- The `save` implementation for `Backtrackable PUnit σ`. -/
@[inline] def dummySave : σ → PUnit := fun _ => ⟨⟩

/-- The `restore` implementation for `Backtrackable PUnit σ`. -/
@[inline] def dummyRestore : σ → PUnit → σ := fun s _ => s

/--
Dummy default instance. This makes every `σ` trivially "backtrackable"
by doing nothing on backtrack. Because this is the first declared instance
of `Backtrackable _ σ`, it will be picked only if there are no other
`Backtrackable _ σ` instances registered.
-/
instance nonBacktrackable : Backtrackable PUnit σ where
  save    := dummySave
  restore := dummyRestore

end EStateM

/-- A class for types that can be hashed into a `UInt64`. -/
class Hashable (α : Sort u) where
  /-- Hashes the value `a : α` into a `UInt64`. -/
  hash : α → UInt64

export Hashable (hash)

/-- An opaque hash mixing operation, used to implement hashing for tuples. -/
@[extern "lean_uint64_mix_hash"]
opaque mixHash (u₁ u₂ : UInt64) : UInt64

instance [Hashable α] {p : α → Prop} : Hashable (Subtype p) where
  hash a := hash a.val

/-- An opaque string hash function. -/
@[extern "lean_string_hash"]
protected opaque String.hash (s : @& String) : UInt64

instance : Hashable String where
  hash := String.hash

namespace Lean

/--
Hierarchical names consist of a sequence of components, each of
which is either a string or numeric, that are written separated by dots (`.`).

Hierarchical names are used to name declarations and for creating
unique identifiers for free variables and metavariables.

You can create hierarchical names using a backtick:
```
`Lean.Meta.whnf
```
It is short for `.str (.str (.str .anonymous "Lean") "Meta") "whnf"`.

You can use double backticks to request Lean to statically check whether the name
corresponds to a Lean declaration in scope.
```
``Lean.Meta.whnf
```
If the name is not in scope, Lean will report an error.

There are two ways to convert a `String` to a `Name`:

 1. `Name.mkSimple` creates a name with a single string component.

 2. `String.toName` first splits the string into its dot-separated
    components, and then creates a hierarchical name.
-/
inductive Name where
  /-- The "anonymous" name. -/
  | anonymous : Name
  /--
  A string name. The name `Lean.Meta.run` is represented at
  ```lean
  .str (.str (.str .anonymous "Lean") "Meta") "run"
  ```
  -/
  | str (pre : Name) (str : String)
  /--
  A numerical name. This kind of name is used, for example, to create hierarchical names for
  free variables and metavariables. The identifier `_uniq.231` is represented as
  ```lean
  .num (.str .anonymous "_uniq") 231
  ```
  -/
  | num (pre : Name) (i : Nat)
with
  /-- A hash function for names, which is stored inside the name itself as a
  computed field. -/
  @[computed_field] hash : Name → UInt64
    | .anonymous => .ofNatLT 1723 (of_decide_eq_true rfl)
    | .str p s => mixHash p.hash s.hash
    | .num p v => mixHash p.hash (dite (LT.lt v UInt64.size) (fun h => UInt64.ofNatLT v h) (fun _ => UInt64.ofNatLT 17 (of_decide_eq_true rfl)))

instance : Inhabited Name where
  default := Name.anonymous

instance : Hashable Name where
  hash := Name.hash

namespace Name

/--
`.str p s` is now the preferred form.
-/
@[export lean_name_mk_string]
abbrev mkStr (p : Name) (s : String) : Name :=
  Name.str p s

/--
`.num p v` is now the preferred form.
-/
@[export lean_name_mk_numeral]
abbrev mkNum (p : Name) (v : Nat) : Name :=
  Name.num p v

/--
Converts a `String` to a `Name` without performing any parsing. `mkSimple s` is short for `.str .anonymous s`.

This means that `mkSimple "a.b"` is the name `«a.b»`, not `a.b`.
-/
abbrev mkSimple (s : String) : Name :=
  .str .anonymous s

/-- Make name `s₁` -/
@[reducible] def mkStr1 (s₁ : String) : Name :=
  .str .anonymous s₁

/-- Make name `s₁.s₂` -/
@[reducible] def mkStr2 (s₁ s₂ : String) : Name :=
  .str (.str .anonymous s₁) s₂

/-- Make name `s₁.s₂.s₃` -/
@[reducible] def mkStr3 (s₁ s₂ s₃ : String) : Name :=
  .str (.str (.str .anonymous s₁) s₂) s₃

/-- Make name `s₁.s₂.s₃.s₄` -/
@[reducible] def mkStr4 (s₁ s₂ s₃ s₄ : String) : Name :=
  .str (.str (.str (.str .anonymous s₁) s₂) s₃) s₄

/-- Make name `s₁.s₂.s₃.s₄.s₅` -/
@[reducible] def mkStr5 (s₁ s₂ s₃ s₄ s₅ : String) : Name :=
  .str (.str (.str (.str (.str .anonymous s₁) s₂) s₃) s₄) s₅

/-- Make name `s₁.s₂.s₃.s₄.s₅.s₆` -/
@[reducible] def mkStr6 (s₁ s₂ s₃ s₄ s₅ s₆ : String) : Name :=
  .str (.str (.str (.str (.str (.str .anonymous s₁) s₂) s₃) s₄) s₅) s₆

/-- Make name `s₁.s₂.s₃.s₄.s₅.s₆.s₇` -/
@[reducible] def mkStr7 (s₁ s₂ s₃ s₄ s₅ s₆ s₇ : String) : Name :=
  .str (.str (.str (.str (.str (.str (.str .anonymous s₁) s₂) s₃) s₄) s₅) s₆) s₇

/-- Make name `s₁.s₂.s₃.s₄.s₅.s₆.s₇.s₈` -/
@[reducible] def mkStr8 (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : String) : Name :=
  .str (.str (.str (.str (.str (.str (.str (.str .anonymous s₁) s₂) s₃) s₄) s₅) s₆) s₇) s₈

/-- (Boolean) equality comparator for names. -/
@[extern "lean_name_eq"]
protected def beq : (@& Name) → (@& Name) → Bool
  | anonymous, anonymous => true
  | str p₁ s₁, str p₂ s₂ => and (BEq.beq s₁ s₂) (Name.beq p₁ p₂)
  | num p₁ n₁, num p₂ n₂ => and (BEq.beq n₁ n₂) (Name.beq p₁ p₂)
  | _,         _         => false

instance : BEq Name where
  beq := Name.beq

/--
This function does not have special support for macro scopes.
See `Name.append`.
-/
def appendCore : Name → Name → Name
  | n, .anonymous => n
  | n, .str p s => .str (appendCore n p) s
  | n, .num p d => .num (appendCore n p) d

end Name

/-- The default maximum recursion depth. This is adjustable using the `maxRecDepth` option. -/
def defaultMaxRecDepth := 512

/-- The message to display on stack overflow. -/
def maxRecDepthErrorMessage : String :=
  "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"

/-! # Syntax -/

/-- Source information of tokens. -/
inductive SourceInfo where
  /--
  Token from original input with whitespace and position information.
  `leading` will be inferred after parsing by `Syntax.updateLeading`. During parsing,
  it is not at all clear what the preceding token was, especially with backtracking.
  -/
  | original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos)
  /--
  Synthesized syntax (e.g. from a quotation) annotated with a span from the original source.
  In the delaborator, we "misuse" this constructor to store synthetic positions identifying
  subterms.

  The `canonical` flag on synthetic syntax is enabled for syntax that is not literally part
  of the original input syntax but should be treated "as if" the user really wrote it
  for the purpose of hovers and error messages. This is usually used on identifiers,
  to connect the binding site to the user's original syntax even if the name of the identifier
  changes during expansion, as well as on tokens where we will attach targeted messages.

  The syntax `token%$stx` in a syntax quotation will annotate the token `token` with the span
  from `stx` and also mark it as canonical.

  As a rough guide, a macro expansion should only use a given piece of input syntax in
  a single canonical token, although this is sometimes violated when the same identifier
  is used to declare two binders, as in the macro expansion for dependent if:
  ```
  `(if $h : $cond then $t else $e) ~>
  `(dite $cond (fun $h => $t) (fun $h => $t))
  ```
  In these cases if the user hovers over `h` they will see information about both binding sites.
  -/
  | synthetic (pos : String.Pos) (endPos : String.Pos) (canonical := false)
  /-- Synthesized token without position information. -/
  | protected none

instance : Inhabited SourceInfo := ⟨SourceInfo.none⟩

namespace SourceInfo

/--
Gets the position information from a `SourceInfo`, if available.
If `canonicalOnly` is true, then `.synthetic` syntax with `canonical := false`
will also return `none`.
-/
def getPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match info, canonicalOnly with
  | original (pos := pos) ..,  _
  | synthetic (pos := pos) (canonical := true) .., _
  | synthetic (pos := pos) .., false => some pos
  | _,                         _     => none

/--
Gets the end position information from a `SourceInfo`, if available.
If `canonicalOnly` is true, then `.synthetic` syntax with `canonical := false`
will also return `none`.
-/
def getTailPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match info, canonicalOnly with
  | original (endPos := endPos) ..,  _
  | synthetic (endPos := endPos) (canonical := true) .., _
  | synthetic (endPos := endPos) .., false => some endPos
  | _,                               _     => none

/--
Gets the substring representing the trailing whitespace of a `SourceInfo`, if available.
-/
def getTrailing? (info : SourceInfo) : Option Substring :=
  match info with
  | original (trailing := trailing) .. => some trailing
  | _                                  => none

/--
Gets the end position information of the trailing whitespace of a `SourceInfo`, if available.
If `canonicalOnly` is true, then `.synthetic` syntax with `canonical := false`
will also return `none`.
-/
def getTrailingTailPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match info.getTrailing? with
  | some trailing => some trailing.stopPos
  | none          => info.getTailPos? canonicalOnly

end SourceInfo

/--
A `SyntaxNodeKind` classifies `Syntax.node` values. It is an abbreviation for
`Name`, and you can use name literals to construct `SyntaxNodeKind`s, but
they need not refer to declarations in the environment. Conventionally, a
`SyntaxNodeKind` will correspond to the `Parser` or `ParserDesc` declaration
that parses it.
-/
abbrev SyntaxNodeKind := Name

/-! # Syntax AST -/

/--
Binding information resolved and stored at compile time of a syntax quotation.
Note: We do not statically know whether a syntax expects a namespace or term name,
so a `Syntax.ident` may contain both preresolution kinds.
-/
inductive Syntax.Preresolved where
  /-- A potential namespace reference -/
  | namespace (ns : Name)
  /-- A potential global constant or section variable reference, with additional field accesses -/
  | decl (n : Name) (fields : List String)

/--
Syntax objects used by the parser, macro expander, delaborator, etc.
-/
inductive Syntax where
  /-- A `missing` syntax corresponds to a portion of the syntax tree that is
  missing because of a parse error. The indexing operator on Syntax also
  returns `missing` for indexing out of bounds. -/
  | missing : Syntax
  /-- Node in the syntax tree.

  The `info` field is used by the delaborator to store the position of the
  subexpression corresponding to this node.
  The parser sets the `info` field to `none`, with position retrieval continuing recursively.
  Nodes created by quotations use the result from `SourceInfo.fromRef` so that they are marked
  as synthetic even when the leading/trailing token is not.
  The delaborator uses the `info` field to store the position of the subexpression
  corresponding to this node.

  (Remark: the `node` constructor did not have an `info` field in previous
  versions. This caused a bug in the interactive widgets, where the popup for
  `a + b` was the same as for `a`. The delaborator used to associate
  subexpressions with pretty-printed syntax by setting the (string) position
  of the first atom/identifier to the (expression) position of the
  subexpression. For example, both `a` and `a + b` have the same first
  identifier, and so their infos got mixed up.) -/
  | node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  /-- An `atom` corresponds to a keyword or piece of literal unquoted syntax.
  These correspond to quoted strings inside `syntax` declarations.
  For example, in `(x + y)`, `"("`, `"+"` and `")"` are `atom`
  and `x` and `y` are `ident`. -/
  | atom   (info : SourceInfo) (val : String) : Syntax
  /-- An `ident` corresponds to an identifier as parsed by the `ident` or
  `rawIdent` parsers.
  * `rawVal` is the literal substring from the input file
  * `val` is the parsed identifier (with hygiene)
  * `preresolved` is the list of possible declarations this could refer to
  -/
  | ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) : Syntax

/-- Create syntax node with 1 child -/
def Syntax.node1 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray1 a₁)

/-- Create syntax node with 2 children -/
def Syntax.node2 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ a₂ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray2 a₁ a₂)

/-- Create syntax node with 3 children -/
def Syntax.node3 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ a₂ a₃ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray3 a₁ a₂ a₃)

/-- Create syntax node with 4 children -/
def Syntax.node4 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ a₂ a₃ a₄ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray4 a₁ a₂ a₃ a₄)

/-- Create syntax node with 5 children -/
def Syntax.node5 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ a₂ a₃ a₄ a₅ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray5 a₁ a₂ a₃ a₄ a₅)

/-- Create syntax node with 6 children -/
def Syntax.node6 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ a₂ a₃ a₄ a₅ a₆ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray6 a₁ a₂ a₃ a₄ a₅ a₆)

/-- Create syntax node with 7 children -/
def Syntax.node7 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray7 a₁ a₂ a₃ a₄ a₅ a₆ a₇)

/-- Create syntax node with 8 children -/
def Syntax.node8 (info : SourceInfo) (kind : SyntaxNodeKind) (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : Syntax) : Syntax :=
  Syntax.node info kind (Array.mkArray8 a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)

/-- `SyntaxNodeKinds` is a set of `SyntaxNodeKind` (implemented as a list). -/
def SyntaxNodeKinds := List SyntaxNodeKind

/--
A `Syntax` value of one of the given syntax kinds.
Note that while syntax quotations produce/expect `TSyntax` values of the correct kinds,
this is not otherwise enforced and can easily be circumvented by direct use of the constructor.
The namespace `TSyntax.Compat` can be opened to expose a general coercion from `Syntax` to any
`TSyntax ks` for porting older code.
-/
structure TSyntax (ks : SyntaxNodeKinds) where
  /-- The underlying `Syntax` value. -/
  raw : Syntax

instance : Inhabited Syntax where
  default := Syntax.missing

instance : Inhabited (TSyntax ks) where
  default := ⟨default⟩

/-! # Builtin kinds -/

/--
The `choice` kind is used when a piece of syntax has multiple parses, and the
determination of which to use is deferred until typing information is available.
-/
abbrev choiceKind : SyntaxNodeKind := `choice

/-- The null kind is used for raw list parsers like `many`. -/
abbrev nullKind : SyntaxNodeKind := `null

/--
The `group` kind is by the `group` parser, to avoid confusing with the null
kind when used inside `optional`.
-/
abbrev groupKind : SyntaxNodeKind := `group

/--
`ident` is not actually used as a node kind, but it is returned by
`getKind` in the `ident` case so that things that handle different node
kinds can also handle `ident`.
-/
abbrev identKind : SyntaxNodeKind := `ident

/-- `str` is the node kind of string literals like `"foo"`. -/
abbrev strLitKind : SyntaxNodeKind := `str

/-- `char` is the node kind of character literals like `'A'`. -/
abbrev charLitKind : SyntaxNodeKind := `char

/-- `num` is the node kind of number literals like `42`. -/
abbrev numLitKind : SyntaxNodeKind := `num

/-- `scientific` is the node kind of floating point literals like `1.23e-3`. -/
abbrev scientificLitKind : SyntaxNodeKind := `scientific

/-- `name` is the node kind of name literals like `` `foo ``. -/
abbrev nameLitKind : SyntaxNodeKind := `name

/-- `fieldIdx` is the node kind of projection indices like the `2` in `x.2`. -/
abbrev fieldIdxKind : SyntaxNodeKind := `fieldIdx

/--
`hygieneInfo` is the node kind of the `hygieneInfo` parser, which is an
"invisible token" which captures the hygiene information at the current point
without parsing anything.

They can be used to generate identifiers (with `Lean.HygieneInfo.mkIdent`)
as if they were introduced by the calling context, not the called macro.
-/
abbrev hygieneInfoKind : SyntaxNodeKind := `hygieneInfo

/--
`interpolatedStrLitKind` is the node kind of interpolated string literal
fragments like `"value = {` and `}"` in `s!"value = {x}"`.
-/
abbrev interpolatedStrLitKind : SyntaxNodeKind := `interpolatedStrLitKind
/--
`interpolatedStrKind` is the node kind of an interpolated string literal
like `"value = {x}"` in `s!"value = {x}"`.
-/
abbrev interpolatedStrKind : SyntaxNodeKind := `interpolatedStrKind

/-- Creates an info-less node of the given kind and children. -/
@[inline] def mkNode (k : SyntaxNodeKind) (args : Array Syntax) : TSyntax (.cons k .nil) :=
  ⟨Syntax.node SourceInfo.none k args⟩

/-- Creates an info-less `nullKind` node with the given children, if any. -/
-- NOTE: used by the quotation elaborator output
@[inline] def mkNullNode (args : Array Syntax := Array.empty) : Syntax :=
  mkNode nullKind args |>.raw

namespace Syntax

/--
Gets the kind of a `Syntax` node. For non-`node` syntax, we use "pseudo kinds":
`identKind` for `ident`, `missing` for `missing`, and the atom's string literal
for atoms.
-/
def getKind (stx : Syntax) : SyntaxNodeKind :=
  match stx with
  | Syntax.node _ k _    => k
  -- We use these "pseudo kinds" for antiquotation kinds.
  -- For example, an antiquotation `$id:ident` (using Lean.Parser.Term.ident)
  -- is compiled to ``if stx.isOfKind `ident ...``
  | Syntax.missing     => `missing
  | Syntax.atom _ v    => Name.mkSimple v
  | Syntax.ident ..    => identKind

/--
Changes the kind at the root of a `Syntax` node to `k`.
Does nothing for non-`node` nodes.
-/
def setKind (stx : Syntax) (k : SyntaxNodeKind) : Syntax :=
  match stx with
  | Syntax.node info _ args => Syntax.node info k args
  | _                       => stx

/-- Is this a syntax with node kind `k`? -/
def isOfKind (stx : Syntax) (k : SyntaxNodeKind) : Bool :=
  beq stx.getKind k

/--
Gets the `i`'th argument of the syntax node. This can also be written `stx[i]`.
Returns `missing` if `i` is out of range.
-/
def getArg (stx : Syntax) (i : Nat) : Syntax :=
  match stx with
  | Syntax.node _ _ args => args.getD i Syntax.missing
  | _                    => Syntax.missing

/-- Gets the list of arguments of the syntax node, or `#[]` if it's not a `node`. -/
def getArgs (stx : Syntax) : Array Syntax :=
  match stx with
  | Syntax.node _ _ args => args
  | _                    => Array.empty

/-- Gets the number of arguments of the syntax node, or `0` if it's not a `node`. -/
def getNumArgs (stx : Syntax) : Nat :=
  match stx with
  | Syntax.node _ _ args => args.size
  | _                    => 0

/--
Assuming `stx` was parsed by `optional`, returns the enclosed syntax
if it parsed something and `none` otherwise.
-/
def getOptional? (stx : Syntax) : Option Syntax :=
  match stx with
  | Syntax.node _ k args => match and (beq k nullKind) (beq args.size 1) with
    | true  => some (args.get!Internal 0)
    | false => none
  | _                    => none

/-- Is this syntax `.missing`? -/
def isMissing : Syntax → Bool
  | Syntax.missing => true
  | _ => false

/-- Is this syntax a `node` with kind `k`? -/
def isNodeOf (stx : Syntax) (k : SyntaxNodeKind) (n : Nat) : Bool :=
  and (stx.isOfKind k) (beq stx.getNumArgs n)

/-- `stx.isIdent` is `true` iff `stx` is an identifier. -/
def isIdent : Syntax → Bool
  | ident .. => true
  | _        => false

/-- If this is an `ident`, return the parsed value, else `.anonymous`. -/
def getId : Syntax → Name
  | ident _ _ val _ => val
  | _               => Name.anonymous

/-- Retrieve the immediate info from the Syntax node. -/
def getInfo? : Syntax → Option SourceInfo
  | atom info ..  => some info
  | ident info .. => some info
  | node info ..  => some info
  | missing       => none

/-- Retrieve the left-most node or leaf's info in the Syntax tree. -/
partial def getHeadInfo? : Syntax → Option SourceInfo
  | atom info _   => some info
  | ident info .. => some info
  | node SourceInfo.none _ args   =>
    let rec loop (i : Nat) : Option SourceInfo :=
      match decide (LT.lt i args.size) with
      | true => match getHeadInfo? (args.get!Internal i) with
         | some info => some info
         | none      => loop (hAdd i 1)
      | false => none
    loop 0
  | node info _ _ => some info
  | _             => none

/-- Retrieve the left-most leaf's info in the Syntax tree, or `none` if there is no token. -/
partial def getHeadInfo (stx : Syntax) : SourceInfo :=
  match stx.getHeadInfo? with
  | some info => info
  | none      => SourceInfo.none

/--
Get the starting position of the syntax, if possible.
If `canonicalOnly` is true, non-canonical `synthetic` nodes are treated as not carrying
position information.
-/
def getPos? (stx : Syntax) (canonicalOnly := false) : Option String.Pos :=
  stx.getHeadInfo.getPos? canonicalOnly

/--
Get the ending position of the syntax, if possible.
If `canonicalOnly` is true, non-canonical `synthetic` nodes are treated as not carrying
position information.
-/
partial def getTailPos? (stx : Syntax) (canonicalOnly := false) : Option String.Pos :=
  match stx, canonicalOnly with
  | atom (SourceInfo.original (endPos := pos) ..) .., _
  | atom (SourceInfo.synthetic (endPos := pos) (canonical := true) ..) _, _
  | atom (SourceInfo.synthetic (endPos := pos) ..) _,  false
  | ident (SourceInfo.original (endPos := pos) ..) .., _
  | ident (SourceInfo.synthetic (endPos := pos) (canonical := true) ..) .., _
  | ident (SourceInfo.synthetic (endPos := pos) ..) .., false
  | node (SourceInfo.original (endPos := pos) ..) .., _
  | node (SourceInfo.synthetic (endPos := pos) (canonical := true) ..) .., _
  | node (SourceInfo.synthetic (endPos := pos) ..) .., false => some pos
  | node _ _ args, _ =>
    let rec loop (i : Nat) : Option String.Pos :=
      match decide (LT.lt i args.size) with
      | true => match getTailPos? (args.get!Internal ((args.size.sub i).sub 1)) canonicalOnly with
         | some info => some info
         | none      => loop (hAdd i 1)
      | false => none
    loop 0
  | _, _ => none

/--
An array of syntax elements interspersed with separators. Can be coerced
to/from `Array Syntax` to automatically remove/insert the separators.
-/
structure SepArray (sep : String) where
  /-- The array of elements and separators, ordered like
  `#[el1, sep1, el2, sep2, el3]`. -/
  elemsAndSeps : Array Syntax

/-- A typed version of `SepArray`. -/
structure TSepArray (ks : SyntaxNodeKinds) (sep : String) where
  /-- The array of elements and separators, ordered like
  `#[el1, sep1, el2, sep2, el3]`. -/
  elemsAndSeps : Array Syntax

end Syntax

/-- An array of syntaxes of kind `ks`. -/
abbrev TSyntaxArray (ks : SyntaxNodeKinds) := Array (TSyntax ks)

/-- Implementation of `TSyntaxArray.raw`. -/
unsafe def TSyntaxArray.rawImpl : TSyntaxArray ks → Array Syntax := unsafeCast

/-- Converts a `TSyntaxArray` to an `Array Syntax`, without reallocation. -/
@[implemented_by TSyntaxArray.rawImpl]
opaque TSyntaxArray.raw (as : TSyntaxArray ks) : Array Syntax := Array.empty

/-- Implementation of `TSyntaxArray.mk`. -/
unsafe def TSyntaxArray.mkImpl : Array Syntax → TSyntaxArray ks := unsafeCast

/-- Converts an `Array Syntax` to a `TSyntaxArray`, without reallocation. -/
@[implemented_by TSyntaxArray.mkImpl]
opaque TSyntaxArray.mk (as : Array Syntax) : TSyntaxArray ks := Array.empty

/-- Constructs a synthetic `SourceInfo` using a `ref : Syntax` for the span. -/
def SourceInfo.fromRef (ref : Syntax) (canonical := false) : SourceInfo :=
  let noncanonical ref :=
    match ref.getPos?, ref.getTailPos? with
    | some pos, some tailPos => .synthetic pos tailPos
    | _,        _            => .none
  match canonical with
  | true =>
    match ref.getPos? true, ref.getTailPos? true with
    | some pos, some tailPos => .synthetic pos tailPos true
    | _,        _            => noncanonical ref
  | false => noncanonical ref

/-- Constructs a synthetic `atom` with no source info. -/
def mkAtom (val : String) : Syntax :=
  Syntax.atom SourceInfo.none val

/-- Constructs a synthetic `atom` with source info coming from `src`. -/
def mkAtomFrom (src : Syntax) (val : String) (canonical := false) : Syntax :=
  Syntax.atom (SourceInfo.fromRef src canonical) val

/-! # Parser descriptions -/

/--
A `ParserDescr` is a grammar for parsers. This is used by the `syntax` command
to produce parsers without having to `import Lean`.
-/
inductive ParserDescr where
  /-- A (named) nullary parser, like `ppSpace` -/
  | const  (name : Name)
  /-- A (named) unary parser, like `group(p)` -/
  | unary  (name : Name) (p : ParserDescr)
  /-- A (named) binary parser, like `orelse` or `andthen`
  (written as `p1 <|> p2` and `p1 p2` respectively in `syntax`) -/
  | binary (name : Name) (p₁ p₂ : ParserDescr)
  /-- Parses using `p`, then pops the stack to create a new node with kind `kind`.
  The precedence `prec` is used to determine whether the parser should apply given
  the current precedence level. -/
  | node (kind : SyntaxNodeKind) (prec : Nat) (p : ParserDescr)
  /-- Like `node` but for trailing parsers (which start with a nonterminal).
  Assumes the lhs is already on the stack, and parses using `p`, then pops the
  stack including the lhs to create a new node with kind `kind`.
  The precedence `prec` and `lhsPrec` are used to determine whether the parser
  should apply. -/
  | trailingNode (kind : SyntaxNodeKind) (prec lhsPrec : Nat) (p : ParserDescr)
  /-- A literal symbol parser: parses `val` as a literal.
  This parser does not work on identifiers, so `symbol` arguments are declared
  as "keywords" and cannot be used as identifiers anywhere in the file. -/
  | symbol (val : String)
  /-- Like `symbol`, but without reserving `val` as a keyword.
  If `includeIdent` is true then `ident` will be reinterpreted as `atom` if it matches. -/
  | nonReservedSymbol (val : String) (includeIdent : Bool)
  /-- Parses using the category parser `catName` with right binding power
  (i.e. precedence) `rbp`. -/
  | cat (catName : Name) (rbp : Nat)
  /-- Parses using another parser `declName`, which can be either
  a `Parser` or `ParserDescr`. -/
  | parser (declName : Name)
  /-- Like `node`, but also declares that the body can be matched using an antiquotation
  with name `name`. For example, `def $id:declId := 1` uses an antiquotation with
  name `declId` in the place where a `declId` is expected. -/
  | nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : ParserDescr)
  /-- A `sepBy(p, sep)` parses 0 or more occurrences of `p` separated by `sep`.
  `psep` is usually the same as `symbol sep`, but it can be overridden.
  `sep` is only used in the antiquot syntax: `$x;*` would match if `sep` is `";"`.
  `allowTrailingSep` is true if e.g. `a, b,` is also allowed to match. -/
  | sepBy  (p : ParserDescr) (sep : String) (psep : ParserDescr) (allowTrailingSep : Bool := false)
  /-- `sepBy1` is just like `sepBy`, except it takes 1 or more instead of
  0 or more occurrences of `p`. -/
  | sepBy1 (p : ParserDescr) (sep : String) (psep : ParserDescr) (allowTrailingSep : Bool := false)

instance : Inhabited ParserDescr where
  default := ParserDescr.symbol ""

/--
Although `TrailingParserDescr` is an abbreviation for `ParserDescr`, Lean will
look at the declared type in order to determine whether to add the parser to
the leading or trailing parser table. The determination is done automatically
by the `syntax` command.
-/
abbrev TrailingParserDescr := ParserDescr

/-!
Runtime support for making quotation terms auto-hygienic, by mangling identifiers
introduced by them with a "macro scope" supplied by the context. Details to appear in a
paper soon.
-/

/--
A macro scope identifier is just a `Nat` that gets bumped every time we
enter a new macro scope. Within a macro scope, all occurrences of identifier `x`
parse to the same thing, but `x` parsed from different macro scopes will
produce different identifiers.
-/
abbrev MacroScope := Nat
/-- Macro scope used internally. It is not available for our frontend. -/
def reservedMacroScope := 0
/-- First macro scope available for our frontend -/
def firstFrontendMacroScope := hAdd reservedMacroScope 1

/--
A `MonadRef` is a monad that has a `ref : Syntax` in the read-only state.
This is used to keep track of the location where we are working; if an exception
is thrown, the `ref` gives the location where the error will be reported,
assuming no more specific location is provided.
-/
class MonadRef (m : Type → Type) where
  /-- Get the current value of the `ref` -/
  getRef      : m Syntax
  /-- Run `x : m α` with a modified value for the `ref` -/
  withRef {α} : Syntax → m α → m α

export MonadRef (getRef)

instance (m n : Type → Type) [MonadLift m n] [MonadFunctor m n] [MonadRef m] : MonadRef n where
  getRef        := liftM (getRef : m _)
  withRef ref x := monadMap (m := m) (MonadRef.withRef ref) x

/--
Replaces `oldRef` with `ref`, unless `ref` has no position info.
This biases us to having a valid span to report an error on.
-/
def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
  match ref.getPos? with
  | some _ => ref
  | _      => oldRef

/--
Run `x : m α` with a modified value for the `ref`. This is not exactly
the same as `MonadRef.withRef`, because it uses `replaceRef` to avoid putting
syntax with bad spans in the state.
-/
@[always_inline, inline]
def withRef [Monad m] [MonadRef m] {α} (ref : Syntax) (x : m α) : m α :=
  bind getRef fun oldRef =>
  let ref := replaceRef ref oldRef
  MonadRef.withRef ref x

/--
If `ref? = some ref`, run `x : m α` with a modified value for the `ref` by calling `withRef`.
Otherwise, run `x` directly.
-/
@[always_inline, inline]
def withRef? [Monad m] [MonadRef m] {α} (ref? : Option Syntax) (x : m α) : m α :=
  match ref? with
  | some ref => withRef ref x
  | _        => x

/-- A monad that supports syntax quotations. Syntax quotations (in term
    position) are monadic values that when executed retrieve the current "macro
    scope" from the monad and apply it to every identifier they introduce
    (independent of whether this identifier turns out to be a reference to an
    existing declaration, or an actually fresh binding during further
    elaboration). We also apply the position of the result of `getRef` to each
    introduced symbol, which results in better error positions than not applying
    any position. -/
class MonadQuotation (m : Type → Type) extends MonadRef m where
  /-- Get the fresh scope of the current macro invocation -/
  getCurrMacroScope : m MacroScope
  /-- Get the module name of the current file. This is used to ensure that
  hygienic names don't clash across multiple files. -/
  getMainModule     : m Name
  /--
  Execute action in a new macro invocation context. This transformer should be
  used at all places that morally qualify as the beginning of a "macro call",
  e.g. `elabCommand` and `elabTerm` in the case of the elaborator. However, it
  can also be used internally inside a "macro" if identifiers introduced by
  e.g. different recursive calls should be independent and not collide. While
  returning an intermediate syntax tree that will recursively be expanded by
  the elaborator can be used for the same effect, doing direct recursion inside
  the macro guarded by this transformer is often easier because one is not
  restricted to passing a single syntax tree. Modelling this helper as a
  transformer and not just a monadic action ensures that the current macro
  scope before the recursive call is restored after it, as expected.
  -/
  withFreshMacroScope {α : Type} : m α → m α

export MonadQuotation (getCurrMacroScope getMainModule withFreshMacroScope)

/-- Construct a synthetic `SourceInfo` from the `ref` in the monad state. -/
@[inline]
def MonadRef.mkInfoFromRefPos [Monad m] [MonadRef m] : m SourceInfo :=
  return SourceInfo.fromRef (← getRef)

instance [MonadFunctor m n] [MonadLift m n] [MonadQuotation m] : MonadQuotation n where
  getCurrMacroScope   := liftM (m := m) getCurrMacroScope
  getMainModule       := liftM (m := m) getMainModule
  withFreshMacroScope := monadMap (m := m) withFreshMacroScope

/-!
We represent a name with macro scopes as
```
<actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
```
Example: suppose the module name is `Init.Data.List.Basic`, and name is `foo.bla`, and macroscopes [2, 5]
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```

We may have to combine scopes from different files/modules.
The main modules being processed is always the right-most one.
This situation may happen when we execute a macro generated in
an imported file in the current file.
```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr._hyg.4
```

The delimiter `_hyg` is used just to improve the `hasMacroScopes` performance.
-/

/-- Does this name have hygienic macro scopes? -/
def Name.hasMacroScopes : Name → Bool
  | str _ s => beq s "_hyg"
  | num p _ => hasMacroScopes p
  | _       => false

private def eraseMacroScopesAux : Name → Name
  | .str p s   => match beq s "_@" with
    | true  => p
    | false => eraseMacroScopesAux p
  | .num p _   => eraseMacroScopesAux p
  | .anonymous => Name.anonymous

/-- Remove the macro scopes from the name. -/
@[export lean_erase_macro_scopes]
def Name.eraseMacroScopes (n : Name) : Name :=
  match n.hasMacroScopes with
  | true  => eraseMacroScopesAux n
  | false => n

private def simpMacroScopesAux : Name → Name
  | .num p i => Name.mkNum (simpMacroScopesAux p) i
  | n        => eraseMacroScopesAux n

/-- Helper function we use to create binder names that do not need to be unique. -/
@[export lean_simp_macro_scopes]
def Name.simpMacroScopes (n : Name) : Name :=
  match n.hasMacroScopes with
  | true  => simpMacroScopesAux n
  | false => n

/--
A `MacroScopesView` represents a parsed hygienic name. `extractMacroScopes`
will decode it from a `Name`, and `.review` will re-encode it. The grammar of a
hygienic name is:
```
<name>._@.(<module_name>.<scopes>)*.<mainModule>._hyg.<scopes>
```
-/
structure MacroScopesView where
  /-- The original (unhygienic) name. -/
  name       : Name
  /-- All the name components `(<module_name>.<scopes>)*` from the imports
  concatenated together. -/
  imported   : Name
  /-- The main module in which this identifier was parsed. -/
  mainModule : Name
  /-- The list of macro scopes. -/
  scopes     : List MacroScope

instance : Inhabited MacroScopesView where
  default := ⟨default, default, default, default⟩

/-- Encode a hygienic name from the parsed pieces. -/
def MacroScopesView.review (view : MacroScopesView) : Name :=
  match view.scopes with
  | List.nil      => view.name
  | List.cons _ _ =>
    let base := (Name.mkStr (Name.appendCore (Name.appendCore (Name.mkStr view.name "_@") view.imported) view.mainModule) "_hyg")
    view.scopes.foldl Name.mkNum base

private def assembleParts : List Name → Name → Name
  | .nil,                acc => acc
  | .cons (.str _ s) ps, acc => assembleParts ps (Name.mkStr acc s)
  | .cons (.num _ n) ps, acc => assembleParts ps (Name.mkNum acc n)
  | _,                   _   => panic "Error: unreachable @ assembleParts"

private def extractImported (scps : List MacroScope) (mainModule : Name) : Name → List Name → MacroScopesView
  | n@(Name.str p str), parts =>
    match beq str "_@" with
    | true  => { name := p, mainModule := mainModule, imported := assembleParts parts Name.anonymous, scopes := scps }
    | false => extractImported scps mainModule p (List.cons n parts)
  | n@(Name.num p _), parts => extractImported scps mainModule p (List.cons n parts)
  | _,                    _     => panic "Error: unreachable @ extractImported"

private def extractMainModule (scps : List MacroScope) : Name → List Name → MacroScopesView
  | n@(Name.str p str), parts =>
    match beq str "_@" with
    | true  => { name := p, mainModule := assembleParts parts Name.anonymous, imported := Name.anonymous, scopes := scps }
    | false => extractMainModule scps p (List.cons n parts)
  | n@(Name.num _ _), acc => extractImported scps (assembleParts acc Name.anonymous) n List.nil
  | _,                    _   => panic "Error: unreachable @ extractMainModule"

private def extractMacroScopesAux : Name → List MacroScope → MacroScopesView
  | Name.num p scp, acc => extractMacroScopesAux p (List.cons scp acc)
  | Name.str p _  , acc => extractMainModule acc p List.nil -- str must be "_hyg"
  | _,                _   => panic "Error: unreachable @ extractMacroScopesAux"

/--
  Revert all `addMacroScope` calls. `v = extractMacroScopes n → n = v.review`.
  This operation is useful for analyzing/transforming the original identifiers, then adding back
  the scopes (via `MacroScopesView.review`). -/
def extractMacroScopes (n : Name) : MacroScopesView :=
  match n.hasMacroScopes with
  | true  => extractMacroScopesAux n List.nil
  | false => { name := n, scopes := List.nil, imported := Name.anonymous, mainModule := Name.anonymous }

/-- Add a new macro scope onto the name `n`, in the given `mainModule`. -/
def addMacroScope (mainModule : Name) (n : Name) (scp : MacroScope) : Name :=
  match n.hasMacroScopes with
  | true =>
    let view := extractMacroScopes n
    match beq view.mainModule mainModule with
    | true  => Name.mkNum n scp
    | false =>
      { view with
        imported   := view.scopes.foldl Name.mkNum (Name.appendCore view.imported view.mainModule)
        mainModule := mainModule
        scopes     := List.cons scp List.nil
      }.review
  | false =>
    Name.mkNum (Name.mkStr (Name.appendCore (Name.mkStr n "_@") mainModule) "_hyg") scp

/--
Appends two names `a` and `b`, propagating macro scopes from `a` or `b`, if any, to the result.
Panics if both `a` and `b` have macro scopes.

This function is used for the `Append Name` instance.

See also `Lean.Name.appendCore`, which appends names without any consideration for macro scopes.
Also consider `Lean.Name.eraseMacroScopes` to erase macro scopes before appending, if appropriate.
-/
def Name.append (a b : Name) : Name :=
  match a.hasMacroScopes, b.hasMacroScopes with
  | true, true  =>
    panic "Error: invalid `Name.append`, both arguments have macro scopes, consider using `eraseMacroScopes`"
  | true, false =>
    let view := extractMacroScopes a
    { view with name := appendCore view.name b }.review
  | false, true =>
    let view := extractMacroScopes b
    { view with name := appendCore a view.name }.review
  | false, false => appendCore a b

instance : Append Name where
  append := Name.append

/--
Add a new macro scope onto the name `n`, using the monad state to supply the
main module and current macro scope.
-/
@[inline] def MonadQuotation.addMacroScope {m : Type → Type} [MonadQuotation m] [Monad m] (n : Name) : m Name :=
  bind getMainModule     fun mainModule =>
  bind getCurrMacroScope fun scp =>
  pure (Lean.addMacroScope mainModule n scp)

namespace Syntax

/-- Is this syntax a null `node`? -/
def matchesNull (stx : Syntax) (n : Nat) : Bool :=
  stx.isNodeOf nullKind n

/--
  Function used for determining whether a syntax pattern `` `(id) `` is matched.
  There are various conceivable notions of when two syntactic identifiers should be regarded as identical,
  but semantic definitions like whether they refer to the same global name cannot be implemented without
  context information (i.e. `MonadResolveName`). Thus in patterns we default to the structural solution
  of comparing the identifiers' `Name` values, though we at least do so modulo macro scopes so that
  identifiers that "look" the same match. This is particularly useful when dealing with identifiers that
  do not actually refer to Lean bindings, e.g. in the `stx` pattern `` `(many($p)) ``. -/
def matchesIdent (stx : Syntax) (id : Name) : Bool :=
  and stx.isIdent (beq stx.getId.eraseMacroScopes id.eraseMacroScopes)

/-- Is this syntax a node kind `k` wrapping an `atom _ val`? -/
def matchesLit (stx : Syntax) (k : SyntaxNodeKind) (val : String) : Bool :=
  match stx with
  | Syntax.node _ k' args => and (beq k k') (match args.getD 0 Syntax.missing with
    | Syntax.atom _ val' => beq val val'
    | _                  => false)
  | _                     => false

end Syntax

namespace Macro

/-- References -/
private opaque MethodsRefPointed : NonemptyType.{0}

private def MethodsRef : Type := MethodsRefPointed.type

instance : Nonempty MethodsRef := MethodsRefPointed.property

/-- The read-only context for the `MacroM` monad. -/
structure Context where
  /-- An opaque reference to the `Methods` object. This is done to break a
  dependency cycle: the `Methods` involve `MacroM` which has not been defined yet. -/
  methods        : MethodsRef
  /-- The currently parsing module. -/
  mainModule     : Name
  /-- The current macro scope. -/
  currMacroScope : MacroScope
  /-- The current recursion depth. -/
  currRecDepth   : Nat := 0
  /-- The maximum recursion depth. -/
  maxRecDepth    : Nat := defaultMaxRecDepth
  /-- The syntax which supplies the position of error messages. -/
  ref            : Syntax

/-- An exception in the `MacroM` monad. -/
inductive Exception where
  /-- A general error, given a message and a span (expressed as a `Syntax`). -/
  | error             : Syntax → String → Exception
  /-- An unsupported syntax exception. We keep this separate because it is
  used for control flow: if one macro does not support a syntax then we try
  the next one. -/
  | unsupportedSyntax : Exception

/-- The mutable state for the `MacroM` monad. -/
structure State where
  /-- The global macro scope counter, used for producing fresh scope names. -/
  macroScope : MacroScope
  /-- The list of trace messages that have been produced, each with a trace
  class and a message. -/
  traceMsgs  : List (Prod Name String) := List.nil
  deriving Inhabited

end Macro

/--
The `MacroM` monad is the main monad for macro expansion. It has the
information needed to handle hygienic name generation, and is the monad that
`macro` definitions live in.

Notably, this is a (relatively) pure monad: there is no `IO` and no access to
the `Environment`. That means that things like declaration lookup are
impossible here, as well as `IO.Ref` or other side-effecting operations.
For more capabilities, macros can instead be written as `elab` using `adaptExpander`.
-/
abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception Macro.State)

/--
A `macro` has type `Macro`, which is a `Syntax → MacroM Syntax`: it
receives an input syntax and is supposed to "expand" it into another piece of
syntax.
-/
abbrev Macro := Syntax → MacroM Syntax

namespace Macro

instance : MonadRef MacroM where
  getRef     := bind read fun ctx => pure ctx.ref
  withRef    := fun ref x => withReader (fun ctx => { ctx with ref := ref }) x

/-- Add a new macro scope to the name `n`. -/
def addMacroScope (n : Name) : MacroM Name :=
  bind read fun ctx =>
  pure (Lean.addMacroScope ctx.mainModule n ctx.currMacroScope)

/-- Throw an `unsupportedSyntax` exception. -/
def throwUnsupported {α} : MacroM α :=
  throw Exception.unsupportedSyntax

/--
Throw an error with the given message,
using the `ref` for the location information.
-/
def throwError {α} (msg : String) : MacroM α :=
  bind getRef fun ref =>
  throw (Exception.error ref msg)

/-- Throw an error with the given message and location information. -/
def throwErrorAt {α} (ref : Syntax) (msg : String) : MacroM α :=
  withRef ref (throwError msg)

/--
Increments the macro scope counter so that inside the body of `x` the macro
scope is fresh.
-/
@[inline] protected def withFreshMacroScope {α} (x : MacroM α) : MacroM α :=
  bind (modifyGet (fun s => (s.macroScope, { s with macroScope := hAdd s.macroScope 1 }))) fun fresh =>
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

/-- Run `x` with an incremented recursion depth counter. -/
@[inline] def withIncRecDepth {α} (ref : Syntax) (x : MacroM α) : MacroM α :=
  bind read fun ctx =>
  match beq ctx.currRecDepth ctx.maxRecDepth with
  | true  => throw (Exception.error ref maxRecDepthErrorMessage)
  | false => withReader (fun ctx => { ctx with currRecDepth := hAdd ctx.currRecDepth 1 }) x

instance : MonadQuotation MacroM where
  getCurrMacroScope ctx := pure ctx.currMacroScope
  getMainModule     ctx := pure ctx.mainModule
  withFreshMacroScope   := Macro.withFreshMacroScope

/-- The opaque methods that are available to `MacroM`. -/
structure Methods where
  /-- Expands macros in the given syntax. A return value of `none` means there
  was nothing to expand. -/
  expandMacro?      : Syntax → MacroM (Option Syntax)
  /-- Get the current namespace in the file. -/
  getCurrNamespace  : MacroM Name
  /-- Check if a given name refers to a declaration. -/
  hasDecl           : Name → MacroM Bool
  /-- Resolves the given name to an overload list of namespaces. -/
  resolveNamespace  : Name → MacroM (List Name)
  /-- Resolves the given name to an overload list of global definitions.
  The `List String` in each alternative is the deduced list of projections
  (which are ambiguous with name components). -/
  resolveGlobalName : Name → MacroM (List (Prod Name (List String)))
  deriving Inhabited

/-- Implementation of `mkMethods`. -/
unsafe def mkMethodsImp (methods : Methods) : MethodsRef :=
  unsafeCast methods

/-- Make an opaque reference to a `Methods`. -/
@[implemented_by mkMethodsImp]
opaque mkMethods (methods : Methods) : MethodsRef

instance : Inhabited MethodsRef where
  default := mkMethods default

/-- Implementation of `getMethods`. -/
unsafe def getMethodsImp : MacroM Methods :=
  bind read fun ctx => pure (unsafeCast (ctx.methods))

/-- Extract the methods list from the `MacroM` state. -/
@[implemented_by getMethodsImp] opaque getMethods : MacroM Methods

/--
`expandMacro? stx` returns `some stxNew` if `stx` is a macro,
and `stxNew` is its expansion.
-/
def expandMacro? (stx : Syntax) : MacroM (Option Syntax) := do
  (← getMethods).expandMacro? stx

/-- Returns `true` if the environment contains a declaration with name `declName` -/
def hasDecl (declName : Name) : MacroM Bool := do
  (← getMethods).hasDecl declName

/-- Gets the current namespace given the position in the file. -/
def getCurrNamespace : MacroM Name := do
  (← getMethods).getCurrNamespace

  /-- Resolves the given name to an overload list of namespaces. -/
def resolveNamespace (n : Name) : MacroM (List Name) := do
  (← getMethods).resolveNamespace n

/--
Resolves the given name to an overload list of global definitions.
The `List String` in each alternative is the deduced list of projections
(which are ambiguous with name components).

Remark: it will not trigger actions associated with reserved names. Recall that Lean
has reserved names. For example, a definition `foo` has a reserved name `foo.def` for theorem
containing stating that `foo` is equal to its definition. The action associated with `foo.def`
automatically proves the theorem. At the macro level, the name is resolved, but the action is not
executed. The actions are executed by the elaborator when converting `Syntax` into `Expr`.
-/
def resolveGlobalName (n : Name) : MacroM (List (Prod Name (List String))) := do
  (← getMethods).resolveGlobalName n

/-- Add a new trace message, with the given trace class and message. -/
def trace (clsName : Name) (msg : String) : MacroM Unit := do
  modify fun s => { s with traceMsgs := List.cons (Prod.mk clsName msg) s.traceMsgs }

end Macro

export Macro (expandMacro?)

namespace PrettyPrinter

/--
The unexpander monad, essentially `Syntax → Option α`. The `Syntax` is the `ref`,
and it has the possibility of failure without an error message.
-/
abbrev UnexpandM := ReaderT Syntax (EStateM Unit Unit)

/--
Function that tries to reverse macro expansions as a post-processing step of delaboration.
While less general than an arbitrary delaborator, it can be declared without importing `Lean`.
Used by the `[app_unexpander]` attribute.
-/
-- a `kindUnexpander` could reasonably be added later
abbrev Unexpander := Syntax → UnexpandM Syntax

instance : MonadQuotation UnexpandM where
  getRef              := read
  withRef ref x       := withReader (fun _ => ref) x
  -- unexpanders should not need to introduce new names
  getCurrMacroScope   := pure 0
  getMainModule       := pure `_fakeMod
  withFreshMacroScope := id

end PrettyPrinter

end Lean
