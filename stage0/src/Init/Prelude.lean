/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude -- Don't import Init, because we're in Init itself

/-!
# Init.Prelude

This is the first file in the lean import hierarchy. It is responsible for setting
up basic definitions, most of which lean already has "built in knowledge" about,
so it is important that they be set up in exactly this way. (For example, lean will
use `PUnit` in the desugaring of `do` notation, or in the pattern match compiler.)

-/

universe u v w

/--
The identity function. `id` takes an implicit argument `α : Sort u`
(a type in any universe), and an argument `a : α`, and returns `a`.

Although this may look like a useless function, one application of the identity
function is to explicitly put a type on an expression. If `e` has type `T`,
and `T'` is definitionally equal to `T`, then `@id T' e` typechecks, and lean
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
@[reducible] def inferInstance {α : Sort u} [i : α] : α := i

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
@[reducible] def inferInstanceAs (α : Sort u) [i : α] : α := i

set_option bootstrap.inductiveCheckResultingUniverse false in
/--
The unit type, the canonical type with one element, named `unit` or `()`.
This is the universe-polymorphic version of `Unit`; it is preferred to use
`Unit` instead where applicable.
For more information about universe levels: [Types as objects](https://leanprover.github.io/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects)
-/
inductive PUnit : Sort u where
  | /-- `PUnit.unit : PUnit` is the canonical element of the unit type. -/
    unit : PUnit

/--
The unit type, the canonical type with one element, named `unit` or `()`.
In other words, it describes only a single value, which consists of said constructor applied
to no arguments whatsoever.
The `Unit` type is similar to `void` in languages derived from C.

`Unit` is actually defined as `PUnit.{0}` where `PUnit` is the universe
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
@[matchPattern] abbrev Unit.unit : Unit := PUnit.unit

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
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
inductive True : Prop where
  | /-- `True` is true, and `True.intro` (or more commonly, `trivial`)
    is the proof. -/
    intro : True

/--
`False` is the empty proposition. Thus, it has no introduction rules.
It represents a contradiction. `False` elimination rule, `False.rec`,
expresses the fact that anything follows from a contradiction.
This rule is sometimes called ex falso (short for ex falso sequitur quodlibet),
or the principle of explosion.
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
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
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
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
@[macroInline] def False.elim {C : Sort u} (h : False) : C :=
  h.rec

/--
Anything follows from two contradictory hypotheses. Example:
```
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
@[macroInline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
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
For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
inductive Eq : α → α → Prop where
  | /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
    equality type. See also `rfl`, which is usually used instead. -/
    refl (a : α) : Eq a a

/-- Non-dependent recursor for the equality type. -/
@[simp] abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

/--
`rfl : a = a` is the unique constructor of the equality type. This is the
same as `Eq.refl` except that it takes `a` implicitly instead of explicitly.

This is a more powerful theorem than it may appear at first, because although
the statement of the theorem is `a = a`, lean will allow anything that is
definitionally equal to that type. So, for instance, `2 + 2 = 4` is proven in
lean by `rfl`, because both sides are the same up to definitional equality.
-/
@[matchPattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

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

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

/--
Equality is symmetric: if `a = b` then `b = a`.

Because this is in the `Eq` namespace, if you have a variable `h : a = b`,
`h.symm` can be used as shorthand for `Eq.symm h` as a proof of `b = a`.

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h ▸ rfl

/--
Equality is transitive: if `a = b` and `b = c` then `a = c`.

Because this is in the `Eq` namespace, if you variables or expressions
`h₁ : a = b` and `h₂ : b = c`, you can use `h₁.trans h₂ : a = c` as shorthand
for `Eq.trans h₁ h₃`.

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
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

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
@[macroInline] def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec a

/--
Congruence in the function argument: if `a₁ = a₂` then `f a₁ = f a₂` for
any (nondependent) function `f`. This is more powerful than it might look at first, because
you can also use a lambda expression for `f` to prove that
`<something containing a₁> = <something containing a₂>`. This function is used
internally by tactics like `congr` and `simp` to apply equalities inside
subterms.

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl

/--
Congruence in both function and argument. If `f₁ = f₂` and `a₁ = a₂` then
`f₁ a₁ = f₂ a₂`. This only works for nondependent functions; the theorem
statement is more complex in the dependent case.

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
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
that `r` is not required to be an equivalance relation. `Quot` is the basic
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
the same type then `a = b` and `HEq a b` ae equivalent.
-/
inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | /-- Reflexivity of heterogeneous equality. -/
    refl (a : α) : HEq a a

/-- A version of `HEq.refl` with an implicit argument. -/
@[matchPattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a :=
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
For more information: [Constructors with Arguments](https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html?highlight=Prod#constructors-with-arguments)
-/
structure Prod (α : Type u) (β : Type v) where
  /-- The first projection out of a pair. if `p : α × β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : α × β` then `p.2 : β`. -/
  snd : β

attribute [unbox] Prod

/--
Similar to `Prod`, but `α` and `β` can be propositions.
We use this Type internally to automatically generate the `brecOn` recursor.
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
  | /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
    inl (h : a) : Or a b
  | /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
    inr (h : b) : Or a b

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

/--
`Bool` is the type of boolean values, `true` and `false`. Classically,
this is equivalent to `Prop` (the type of propositions), but the distinction
is important for programming, because values of type `Prop` are erased in the
code generator, while `Bool` corresponds to the type called `bool` or `boolean`
in most programming languages.
-/
inductive Bool : Type where
  | /-- The boolean value `false`, not to be confused with the proposition `False`. -/
    false : Bool
  | /-- The boolean value `true`, not to be confused with the proposition `True`. -/
    true : Bool

export Bool (false true)

/--
`Subtype p`, usually written as `{x : α // p x}`, is a type which
represents all the elements `x : α` for which `p x` is true. It is structurally
a pair-like type, so if you have `x : α` and `h : p x` then
`⟨x, h⟩ : {x // p x}`. An element `s : {x // p x}` will coerce to `α` but
you can also make it explicit using `s.1` or `s.val`.
-/
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
up, lean will wait to solve it until `?γ` is known, but then it will run
typeclass inference, and take the first solution it finds, for any value of `?α`,
which thereby determines what `?α` should be.

This expresses that in a term like `a ∈ s`, `s` might be a `Set α` or
`List α` or some other type with a membership operation, and in each case
the "member" type `α` is determined by looking at the container type.
-/
@[reducible] def outParam (α : Sort u) : Sort u := α

set_option linter.unusedVariables.funArgs false in
/-- Auxiliary declaration used to implement named patterns like `x@h:p`. -/
@[reducible] def namedPattern {α : Sort u} (x a : α) (h : Eq x a) : α := a

/--
Auxiliary axiom used to implement `sorry`.

The `sorry` term/tactic expands to `sorryAx _ (synthetic := false)`. This is a
proof of anything, which is intended for stubbing out incomplete parts of a
proof while still having a syntactically correct proof skeleton. Lean will give
a warning whenever a proof uses `sorry`, so you aren't likely to miss it, but
you can double check if a theorem depends on `sorry` by using
`#print axioms my_thm` and looking for `sorryAx` in the axiom list.

The `synthetic` flag is false when written explicitly by the user, but it is
set to `true` when a tactic fails to prove a goal, or if there is a type error
in the expression. A synthetic `sorry` acts like a regular one, except that it
suppresses follow-up errors in order to prevent one error from causing a cascade
of other errors because the desired term was not constructed.
-/
@[extern "lean_sorry", neverExtract]
axiom sorryAx (α : Sort u) (synthetic := false) : α

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
  | /-- If `val : α`, then `α` is nonempty. -/
    intro (val : α) : Nonempty α

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

In lean, we use the axiom of choice to derive the law of excluded middle
(see `Classical.em`), so it will often show up in axiom listings where you
may not expect. You can use `#print axioms my_thm` to find out if a given
theorem depends on this or other axioms.

This axiom can be used to construct "data", but obviously there is no algorithm
to compute it, so lean will require you to mark any definition that would
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
protected def Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
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

instance (α : Sort u) {β : Sort v} [Nonempty β] : Nonempty (α → β) :=
  Nonempty.intro fun _ => Classical.ofNonempty

instance (α : Sort u) {β : α → Sort v} [(a : α) → Nonempty (β a)] : Nonempty ((a : α) → β a) :=
  Nonempty.intro fun _ => Classical.ofNonempty

instance : Inhabited (Sort u) where
  default := PUnit

instance (α : Sort u) {β : Sort v} [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default

instance (α : Sort u) {β : α → Sort v} [(a : α) → Inhabited (β a)] : Inhabited ((a : α) → β a) where
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
-/
class inductive Decidable (p : Prop) where
  | /-- Prove that `p` is decidable by supplying a proof of `¬p` -/
    isFalse (h : Not p) : Decidable p
  | /-- Prove that `p` is decidable by supplying a proof of `p` -/
    isTrue (h : p) : Decidable p

/--
Convert a decidable proposition into a boolean value.

If `p : Prop` is decidable, then `decide p : Bool` is the boolean value
which is `true` if `p` is true and `false` if `p` is false.
-/
@[inlineIfReduce, nospecialize] def Decidable.decide (p : Prop) [h : Decidable p] : Bool :=
  h.casesOn (fun _ => false) (fun _ => true)

export Decidable (isTrue isFalse decide)

/-- A decidable predicate. See `Decidable`. -/
abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)

/-- A decidable relation. See `Decidable`. -/
abbrev DecidableRel {α : Sort u} (r : α → α → Prop) :=
  (a b : α) → Decidable (r a b)

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

@[inline] instance : DecidableEq Bool :=
  fun a b => match a, b with
   | false, false => isTrue rfl
   | false, true  => isFalse (fun h => Bool.noConfusion h)
   | true, false  => isFalse (fun h => Bool.noConfusion h)
   | true, true   => isTrue rfl

/--
`BEq α` is a typeclass for supplying a boolean-valued equality relation on
`α`, notated as `a == b`. Unlike `DecidableEq α` (which uses `a = b`), this
is `Bool` valued instead of `Prop` valued, and it also does not have any
axioms like being reflexive or agreeing with `=`. It is mainly intended for
programming applications. See `LawfulBEq` for a version that requires that
`==` and `=` coincide.
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
For example, `Array.get arr ⟨i, h⟩` expects a proof `h : i < arr.size` in order to
avoid a bounds check, so you can write `if h : i < arr.size then arr.get ⟨i, h⟩ else ...`
to avoid the bounds check inside the if branch. (Of course in this case we have only
lifted the check into an explicit `if`, but we could also use this proof multiple times
or derive `i < arr.size` from some other proposition that we are checking in the `if`.)
-/
@[macroInline] def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  h.casesOn e t

/-! # if-then-else -/

/--
`if c then t else e` is notation for `ite c t e`, "if-then-else", which decides to
return `t` or `e` depending on whether `c` is true or false. The explicit argument
`c : Prop` does not have any actual computational content, but there is an additional
`[Decidable c]` argument synthesized by typeclass inference which actually
determines how to evaluate `c` to true or false.

Because lean uses a strict (call-by-value) evaluation strategy, the signature of this
function is problematic in that it would require `t` and `e` to be evaluated before
calling the `ite` function, which would cause both sides of the `if` to be evaluated.
Even if the result is discarded, this would be a big performance problem,
and is undesirable for users in any case. To resolve this, `ite` is marked as
`@[macroInline]`, which means that it is unfolded during code generation, and
the definition of the function uses `fun _ => t` and `fun _ => e` so this recovers
the expected "lazy" behavior of `if`: the `t` and `e` arguments delay evaluation
until `c` is known.
-/
@[macroInline] def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  h.casesOn (fun _ => e) (fun _ => t)

@[macroInline] instance {p q} [dp : Decidable p] [dq : Decidable q] : Decidable (And p q) :=
  match dp with
  | isTrue  hp =>
    match dq with
    | isTrue hq  => isTrue ⟨hp, hq⟩
    | isFalse hq => isFalse (fun h => hq (And.right h))
  | isFalse hp =>
    isFalse (fun h => hp (And.left h))

@[macroInline] instance [dp : Decidable p] [dq : Decidable q] : Decidable (Or p q) :=
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
boolean condition. This is `@[macroInline]` because `x` and `y` should not
be eagerly evaluated (see `ite`).
-/
@[macroInline] def cond {α : Type u} (c : Bool) (x y : α) : α :=
  match c with
  | true  => x
  | false => y

@[macroInline] def or (x y : Bool) : Bool :=
  match x with
  | true  => true
  | false => y

@[macroInline] def and (x y : Bool) : Bool :=
  match x with
  | false => false
  | true  => y

@[inline] def not : Bool → Bool
  | true  => false
  | false => true

/-- The type of natural numbers. `0`, `1`, `2`, ...-/
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

instance : Inhabited Nat where
  default := Nat.zero

/-- For numeric literals notation -/
class OfNat (α : Type u) (_ : Nat) where
  ofNat : α

@[defaultInstance 100] /- low prio -/
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class LE (α : Type u) where le : α → α → Prop
class LT (α : Type u) where lt : α → α → Prop

@[reducible] def GE.ge {α : Type u} [LE α] (a b : α) : Prop := LE.le b a
@[reducible] def GT.gt {α : Type u} [LT α] (a b : α) : Prop := LT.lt b a

@[inline] def max [LT α] [DecidableRel (@LT.lt α _)] (a b : α) : α :=
  ite (LT.lt b a) a b

@[inline] def min [LE α] [DecidableRel (@LE.le α _)] (a b : α) : α :=
  ite (LE.le a b) a b

/-- Transitive chaining of proofs, used e.g. by `calc`. -/
class Trans (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) where
  trans : r a b → s b c → t a c

export Trans (trans)

instance (r : α → γ → Sort u) : Trans Eq r r where
  trans heq h' := heq ▸ h'

instance (r : α → β → Sort u) : Trans r Eq r where
  trans h' heq := heq ▸ h'

class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAdd : α → β → γ

class HSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSub : α → β → γ

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class HDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hDiv : α → β → γ

class HMod (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMod : α → β → γ

class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hPow : α → β → γ

class HAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAppend : α → β → γ

class HOrElse (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hOrElse : α → (Unit → β) → γ

class HAndThen (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAndThen : α → (Unit → β) → γ

class HAnd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAnd : α → β → γ

class HXor (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hXor : α → β → γ

class HOr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hOr : α → β → γ

class HShiftLeft (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hShiftLeft : α → β → γ

class HShiftRight (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hShiftRight : α → β → γ

class Add (α : Type u) where
  add : α → α → α

class Sub (α : Type u) where
  sub : α → α → α

class Mul (α : Type u) where
  mul : α → α → α

class Neg (α : Type u) where
  neg : α → α

class Div (α : Type u) where
  div : α → α → α

class Mod (α : Type u) where
  mod : α → α → α

class Pow (α : Type u) (β : Type v) where
  pow : α → β → α

class Append (α : Type u) where
  append : α → α → α

class OrElse (α : Type u) where
  orElse  : α → (Unit → α) → α

class AndThen (α : Type u) where
  andThen : α → (Unit → α) → α

class AndOp (α : Type u) where
  and : α → α → α

class Xor (α : Type u) where
  xor : α → α → α

class OrOp (α : Type u) where
  or : α → α → α

class Complement (α : Type u) where
  complement : α → α

class ShiftLeft (α : Type u) where
  shiftLeft : α → α → α

class ShiftRight (α : Type u) where
  shiftRight : α → α → α

@[defaultInstance]
instance [Add α] : HAdd α α α where
  hAdd a b := Add.add a b

@[defaultInstance]
instance [Sub α] : HSub α α α where
  hSub a b := Sub.sub a b

@[defaultInstance]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

@[defaultInstance]
instance [Div α] : HDiv α α α where
  hDiv a b := Div.div a b

@[defaultInstance]
instance [Mod α] : HMod α α α where
  hMod a b := Mod.mod a b

@[defaultInstance]
instance [Pow α β] : HPow α β α where
  hPow a b := Pow.pow a b

@[defaultInstance]
instance [Append α] : HAppend α α α where
  hAppend a b := Append.append a b

@[defaultInstance]
instance [OrElse α] : HOrElse α α α where
  hOrElse a b := OrElse.orElse a b

@[defaultInstance]
instance [AndThen α] : HAndThen α α α where
  hAndThen a b := AndThen.andThen a b

@[defaultInstance]
instance [AndOp α] : HAnd α α α where
  hAnd a b := AndOp.and a b

@[defaultInstance]
instance [Xor α] : HXor α α α where
  hXor a b := Xor.xor a b

@[defaultInstance]
instance [OrOp α] : HOr α α α where
  hOr a b := OrOp.or a b

@[defaultInstance]
instance [ShiftLeft α] : HShiftLeft α α α where
  hShiftLeft a b := ShiftLeft.shiftLeft a b

@[defaultInstance]
instance [ShiftRight α] : HShiftRight α α α where
  hShiftRight a b := ShiftRight.shiftRight a b

open HAdd (hAdd)
open HMul (hMul)
open HPow (hPow)
open HAppend (hAppend)

class Membership (α : outParam (Type u)) (γ : Type v) where
  mem : α → γ → Prop

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

instance : Add Nat where
  add := Nat.add

/- We mark the following definitions as pattern to make sure they can be used in recursive equations,
   and reduced by the equation Compiler. -/
attribute [matchPattern] Nat.add Add.add HAdd.hAdd Neg.neg

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_mul"]
protected def Nat.mul : (@& Nat) → (@& Nat) → Nat
  | _, 0          => 0
  | a, Nat.succ b => Nat.add (Nat.mul a b) a

instance : Mul Nat where
  mul := Nat.mul

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_pow"]
protected def Nat.pow (m : @& Nat) : (@& Nat) → Nat
  | 0      => 1
  | succ n => Nat.mul (Nat.pow m n) m

instance : Pow Nat Nat where
  pow := Nat.pow

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_dec_eq"]
def Nat.beq : (@& Nat) → (@& Nat) → Bool
  | zero,   zero   => true
  | zero,   succ _ => false
  | succ _, zero   => false
  | succ n, succ m => beq n m

instance : BEq Nat where
  beq := Nat.beq

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

@[reducible, extern "lean_nat_dec_eq"]
protected def Nat.decEq (n m : @& Nat) : Decidable (Eq n m) :=
  match h:beq n m with
  | true  => isTrue (eq_of_beq_eq_true h)
  | false => isFalse (ne_of_beq_eq_false h)

@[inline] instance : DecidableEq Nat := Nat.decEq

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_dec_le"]
def Nat.ble : @& Nat → @& Nat → Bool
  | zero,   zero   => true
  | zero,   succ _ => true
  | succ _, zero   => false
  | succ n, succ m => ble n m

protected inductive Nat.le (n : Nat) : Nat → Prop
  | refl     : Nat.le n n
  | step {m} : Nat.le n m → Nat.le n (succ m)

instance : LE Nat where
  le := Nat.le

protected def Nat.lt (n m : Nat) : Prop :=
  Nat.le (succ n) m

instance : LT Nat where
  lt := Nat.lt

theorem Nat.not_succ_le_zero : ∀ (n : Nat), LE.le (succ n) 0 → False
  | 0,      h => nomatch h
  | succ _, h => nomatch h

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
@[extern c inline "lean_nat_sub(#1, lean_box(1))"]
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

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_sub"]
protected def Nat.sub : (@& Nat) → (@& Nat) → Nat
  | a, 0      => a
  | a, succ b => pred (Nat.sub a b)

instance : Sub Nat where
  sub := Nat.sub

@[extern "lean_system_platform_nbits"] opaque System.Platform.getNumBits : Unit → Subtype fun (n : Nat) => Or (Eq n 32) (Eq n 64) :=
  fun _ => ⟨64, Or.inr rfl⟩ -- inhabitant

/-- Gets the word size of the platform.
That is, whether the platform is 64 or 32 bits. -/
def System.Platform.numBits : Nat :=
  (getNumBits ()).val

theorem System.Platform.numBits_eq : Or (Eq numBits 32) (Eq numBits 64) :=
  (getNumBits ()).property

/-- `Fin n` is a natural number `i` with the constraint that `0 ≤ i < n`. -/
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n

theorem Fin.eq_of_val_eq {n} : ∀ {i j : Fin n}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Fin.val_eq_of_eq {n} {i j : Fin n} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

theorem Fin.ne_of_val_ne {n} {i j : Fin n} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

instance (n : Nat) : DecidableEq (Fin n) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (Fin.eq_of_val_eq h)
    | isFalse h => isFalse (Fin.ne_of_val_ne h)

instance {n} : LT (Fin n) where
  lt a b := LT.lt a.val b.val

instance {n} : LE (Fin n) where
  le a b := LE.le a.val b.val

instance Fin.decLt {n} (a b : Fin n) : Decidable (LT.lt a b)  := Nat.decLt ..
instance Fin.decLe {n} (a b : Fin n) : Decidable (LE.le a b) := Nat.decLe ..

def UInt8.size : Nat := 256
/-- Unsigned 8-bit integer. -/
structure UInt8 where
  val : Fin UInt8.size

attribute [extern "lean_uint8_of_nat_mk"] UInt8.mk
attribute [extern "lean_uint8_to_nat"] UInt8.val

@[extern "lean_uint8_of_nat"]
def UInt8.ofNatCore (n : @& Nat) (h : LT.lt n UInt8.size) : UInt8 := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint8_dec_eq"]
def UInt8.decEq (a b : UInt8) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt8.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt8 := UInt8.decEq

instance : Inhabited UInt8 where
  default := UInt8.ofNatCore 0 (by decide)

def UInt16.size : Nat := 65536
/-- Unsigned 16-bit integer. -/
structure UInt16 where
  val : Fin UInt16.size

attribute [extern "lean_uint16_of_nat_mk"] UInt16.mk
attribute [extern "lean_uint16_to_nat"] UInt16.val

@[extern "lean_uint16_of_nat"]
def UInt16.ofNatCore (n : @& Nat) (h : LT.lt n UInt16.size) : UInt16 := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint16_dec_eq"]
def UInt16.decEq (a b : UInt16) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt16.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt16 := UInt16.decEq

instance : Inhabited UInt16 where
  default := UInt16.ofNatCore 0 (by decide)

def UInt32.size : Nat := 4294967296
/-- Unsigned, 32-bit integer. -/
structure UInt32 where
  val : Fin UInt32.size

attribute [extern "lean_uint32_of_nat_mk"] UInt32.mk
attribute [extern "lean_uint32_to_nat"] UInt32.val

@[extern "lean_uint32_of_nat"]
def UInt32.ofNatCore (n : @& Nat) (h : LT.lt n UInt32.size) : UInt32 := {
  val := { val := n, isLt := h }
}

@[extern "lean_uint32_to_nat"]
def UInt32.toNat (n : UInt32) : Nat := n.val.val

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint32_dec_eq"]
def UInt32.decEq (a b : UInt32) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt32.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt32 := UInt32.decEq

instance : Inhabited UInt32 where
  default := UInt32.ofNatCore 0 (by decide)

instance : LT UInt32 where
  lt a b := LT.lt a.val b.val

instance : LE UInt32 where
  le a b := LE.le a.val b.val

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint32_dec_lt"]
def UInt32.decLt (a b : UInt32) : Decidable (LT.lt a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (LT.lt n m))

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint32_dec_le"]
def UInt32.decLe (a b : UInt32) : Decidable (LE.le a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (LE.le n m))

instance (a b : UInt32) : Decidable (LT.lt a b) := UInt32.decLt a b
instance (a b : UInt32) : Decidable (LE.le a b) := UInt32.decLe a b

def UInt64.size : Nat := 18446744073709551616
/-- Unsigned, 64-bit integer. -/
structure UInt64 where
  val : Fin UInt64.size

attribute [extern "lean_uint64_of_nat_mk"] UInt64.mk
attribute [extern "lean_uint64_to_nat"] UInt64.val

@[extern "lean_uint64_of_nat"]
def UInt64.ofNatCore (n : @& Nat) (h : LT.lt n UInt64.size) : UInt64 := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint64_dec_eq"]
def UInt64.decEq (a b : UInt64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt64.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt64 := UInt64.decEq

instance : Inhabited UInt64 where
  default := UInt64.ofNatCore 0 (by decide)

def USize.size : Nat := hPow 2 System.Platform.numBits

theorem usize_size_eq : Or (Eq USize.size 4294967296) (Eq USize.size 18446744073709551616) :=
  show Or (Eq (hPow 2 System.Platform.numBits) 4294967296) (Eq (hPow 2 System.Platform.numBits) 18446744073709551616) from
  match System.Platform.numBits, System.Platform.numBits_eq with
  | _, Or.inl rfl => Or.inl (by decide)
  | _, Or.inr rfl => Or.inr (by decide)

/-- A USize is an unsigned integer with the size of a word
for the platform's architecture.

For example, if running on a 32-bit machine, USize is equivalent to UInt32.
Or on a 64-bit machine, UInt64.
-/
structure USize where
  val : Fin USize.size

attribute [extern "lean_usize_of_nat_mk"] USize.mk
attribute [extern "lean_usize_to_nat"] USize.val

@[extern "lean_usize_of_nat"]
def USize.ofNatCore (n : @& Nat) (h : LT.lt n USize.size) : USize := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern "lean_usize_dec_eq"]
def USize.decEq (a b : USize) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h =>isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => USize.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq USize := USize.decEq

instance : Inhabited USize where
  default := USize.ofNatCore 0 (match USize.size, usize_size_eq with
    | _, Or.inl rfl => by decide
    | _, Or.inr rfl => by decide)

@[extern "lean_usize_of_nat"]
def USize.ofNat32 (n : @& Nat) (h : LT.lt n 4294967296) : USize := {
  val := {
    val  := n
    isLt := match USize.size, usize_size_eq with
      | _, Or.inl rfl => h
      | _, Or.inr rfl => Nat.lt_trans h (by decide)
  }
}

abbrev Nat.isValidChar (n : Nat) : Prop :=
  Or (LT.lt n 0xd800) (And (LT.lt 0xdfff n) (LT.lt n 0x110000))

abbrev UInt32.isValidChar (n : UInt32) : Prop :=
  n.toNat.isValidChar

/-- The `Char` Type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure Char where
  val   : UInt32
  valid : val.isValidChar

private theorem isValidChar_UInt32 {n : Nat} (h : n.isValidChar) : LT.lt n UInt32.size :=
  match h with
  | Or.inl h      => Nat.lt_trans h (by decide)
  | Or.inr ⟨_, h⟩ => Nat.lt_trans h (by decide)

@[extern "lean_uint32_of_nat"]
def Char.ofNatAux (n : @& Nat) (h : n.isValidChar) : Char :=
  { val := ⟨{ val := n, isLt := isValidChar_UInt32 h }⟩, valid := h }

@[noinline, matchPattern]
def Char.ofNat (n : Nat) : Char :=
  dite (n.isValidChar)
    (fun h => Char.ofNatAux n h)
    (fun _ => { val := ⟨{ val := 0, isLt := by decide }⟩, valid := Or.inl (by decide) })

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

def Char.utf8Size (c : Char) : UInt32 :=
  let v := c.val
  ite (LE.le v (UInt32.ofNatCore 0x7F (by decide)))
    (UInt32.ofNatCore 1 (by decide))
    (ite (LE.le v (UInt32.ofNatCore 0x7FF (by decide)))
      (UInt32.ofNatCore 2 (by decide))
      (ite (LE.le v (UInt32.ofNatCore 0xFFFF (by decide)))
        (UInt32.ofNatCore 3 (by decide))
        (UInt32.ofNatCore 4 (by decide))))

inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α

attribute [unbox] Option

export Option (none some)

instance {α} : Inhabited (Option α) where
  default := none

@[macroInline] def Option.getD : Option α → α → α
  | some x, _ => x
  | none,   e => e

@[inline] protected def Option.map (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none   => none

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

instance {α} : Inhabited (List α) where
  default := List.nil

protected def List.hasDecEq {α: Type u} [DecidableEq α] : (a b : List α) → Decidable (Eq a b)
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

@[specialize]
def List.foldl {α β} (f : α → β → α) : (init : α) → List β → α
  | a, nil      => a
  | a, cons b l => foldl f (f a b) l

def List.set : List α → Nat → α → List α
  | cons _ as, 0,          b => cons b as
  | cons a as, Nat.succ n, b => cons a (set as n b)
  | nil,       _,          _ => nil

def List.length : List α → Nat
  | nil       => 0
  | cons _ as => HAdd.hAdd (length as) 1

def List.lengthTRAux : List α → Nat → Nat
  | nil,       n => n
  | cons _ as, n => lengthTRAux as (Nat.succ n)

def List.lengthTR (as : List α) : Nat :=
  lengthTRAux as 0

@[simp] theorem List.length_cons {α} (a : α) (as : List α) : Eq (cons a as).length as.length.succ :=
  rfl

def List.concat {α : Type u} : List α → α → List α
  | nil,       b => cons b nil
  | cons a as, b => cons a (concat as b)

def List.get {α : Type u} : (as : List α) → Fin as.length → α
  | cons a _,  ⟨0, _⟩ => a
  | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩

structure String where
  data : List Char

attribute [extern "lean_string_mk"] String.mk
attribute [extern "lean_string_data"] String.data

@[extern "lean_string_dec_eq"]
def String.decEq (s₁ s₂ : @& String) : Decidable (Eq s₁ s₂) :=
  match s₁, s₂ with
  | ⟨s₁⟩, ⟨s₂⟩ =>
    dite (Eq s₁ s₂) (fun h => isTrue (congrArg _ h)) (fun h => isFalse (fun h' => String.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq String := String.decEq

/-- A byte position in a `String`. Internally, `String`s are UTF-8 encoded.
Codepoint positions (counting the Unicode codepoints rather than bytes)
are represented by plain `Nat`s instead.
Indexing a `String` by a byte position is constant-time, while codepoint
positions need to be translated internally to byte positions in linear-time. -/
structure String.Pos where
  byteIdx : Nat := 0

instance : Inhabited String.Pos where
  default := {}

instance : DecidableEq String.Pos :=
  fun ⟨a⟩ ⟨b⟩ => match decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun he => String.Pos.noConfusion he fun he => absurd he h)

structure Substring where
  str      : String
  startPos : String.Pos
  stopPos  : String.Pos

instance : Inhabited Substring where
  default := ⟨"", {}, {}⟩

@[inline] def Substring.bsize : Substring → Nat
  | ⟨_, b, e⟩ => e.byteIdx.sub b.byteIdx

def String.csize (c : Char) : Nat :=
  c.utf8Size.toNat

@[extern "lean_string_utf8_byte_size"]
def String.utf8ByteSize : (@& String) → Nat
  | ⟨s⟩ => go s
where
  go : List Char → Nat
   | .nil       => 0
   | .cons c cs => hAdd (go cs) (csize c)

instance : HAdd String.Pos String.Pos String.Pos where
  hAdd p₁ p₂ := { byteIdx := hAdd p₁.byteIdx p₂.byteIdx }

instance : HSub String.Pos String.Pos String.Pos where
  hSub p₁ p₂ := { byteIdx := HSub.hSub p₁.byteIdx p₂.byteIdx }

instance : HAdd String.Pos Char String.Pos where
  hAdd p c := { byteIdx := hAdd p.byteIdx (String.csize c) }

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

@[inline] def String.endPos (s : String) : String.Pos :=
  { byteIdx := utf8ByteSize s }

@[inline] def String.toSubstring (s : String) : Substring := {
  str      := s
  startPos := {}
  stopPos  := s.endPos
}

unsafe def unsafeCast {α : Sort u} {β : Sort v} (a : α) : β :=
  PLift.down (ULift.down.{max u v} (cast lcProof (ULift.up.{max u v} (PLift.up a))))

@[neverExtract, extern "lean_panic_fn"]
opaque panicCore {α : Type u} [Inhabited α] (msg : String) : α

/--
  This is workaround for `panic` occurring in monadic code. See issue #695.
  The `panicCore` definition cannot be specialized since it is an extern.
  When `panic` occurs in monadic code, the `Inhabited α` parameter depends on a `[inst : Monad m]` instance.
  The `inst` parameter will not be eliminated during specialization if it occurs inside of a binder (to avoid work duplication), and
  will prevent the the actual monad from being "copied" to the code being specialized. When we reimplement the specializer, we
  may consider copying `inst` if it also occurs outside binders or if it is an instance.
-/
@[noinline, neverExtract]
def panic {α : Type u} [Inhabited α] (msg : String) : α :=
  panicCore msg

-- TODO: this be applied directly to `Inhabited`'s definition when we remove the above workaround
attribute [nospecialize] Inhabited

class GetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop)) where
  getElem (xs : cont) (i : idx) (h : dom xs i) : elem

export GetElem (getElem)

/--
The Compiler has special support for arrays.
They are implemented using dynamic arrays: https://en.wikipedia.org/wiki/Dynamic_array
-/
structure Array (α : Type u) where
  data : List α

attribute [extern "lean_array_data"] Array.data
attribute [extern "lean_array_mk"] Array.mk

/-- The parameter `c` is the initial capacity -/
@[extern "lean_mk_empty_array_with_capacity"]
def Array.mkEmpty {α : Type u} (c : @& Nat) : Array α := {
  data := List.nil
}

def Array.empty {α : Type u} : Array α :=
  mkEmpty 0

@[reducible, extern "lean_array_get_size"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
 a.data.length

@[extern "lean_array_fget"]
def Array.get {α : Type u} (a : @& Array α) (i : @& Fin a.size) : α :=
  a.data.get i

@[inline] abbrev Array.getD (a : Array α) (i : Nat) (v₀ : α) : α :=
  dite (LT.lt i a.size) (fun h => a.get ⟨i, h⟩) (fun _ => v₀)

/-- "Comfortable" version of `fget`. It performs a bound check at runtime. -/
@[extern "lean_array_get"]
def Array.get! {α : Type u} [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
  Array.getD a i default

instance : GetElem (Array α) Nat α fun xs i => LT.lt i xs.size where
  getElem xs i h := xs.get ⟨i, h⟩

@[extern "lean_array_push"]
def Array.push {α : Type u} (a : Array α) (v : α) : Array α := {
  data := List.concat a.data v
}

@[extern "lean_array_fset"]
def Array.set (a : Array α) (i : @& Fin a.size) (v : α) : Array α := {
  data := a.data.set i.val v
}

@[inline] def Array.setD (a : Array α) (i : Nat) (v : α) : Array α :=
  dite (LT.lt i a.size) (fun h => a.set ⟨i, h⟩ v) (fun _ => a)

@[extern "lean_array_set"]
def Array.set! (a : Array α) (i : @& Nat) (v : α) : Array α :=
  Array.setD a i v

-- Slower `Array.append` used in quotations.
protected def Array.appendCore {α : Type u}  (as : Array α) (bs : Array α) : Array α :=
  let rec loop (i : Nat) (j : Nat) (as : Array α) : Array α :=
    dite (LT.lt j bs.size)
      (fun hlt =>
        match i with
        | 0           => as
        | Nat.succ i' => loop i' (hAdd j 1) (as.push (bs.get ⟨j, hlt⟩)))
      (fun _ => as)
  loop bs.size 0 as

@[inlineIfReduce]
def List.toArrayAux : List α → Array α → Array α
  | nil,       r => r
  | cons a as, r => toArrayAux as (r.push a)

@[inlineIfReduce]
def List.redLength : List α → Nat
  | nil       => 0
  | cons _ as => as.redLength.succ

@[inline, matchPattern, export lean_list_to_array]
def List.toArray (as : List α) : Array α :=
  as.toArrayAux (Array.mkEmpty as.redLength)

class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

export Bind (bind)

class Pure (f : Type u → Type v) where
  pure {α : Type u} : α → f α

export Pure (pure)

class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map      : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)

class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq  : {α β : Type u} → f (α → β) → (Unit → f α) → f β

class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β

class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b

class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()

instance {α : Type u} {m : Type u → Type v} [Monad m] : Inhabited (α → m α) where
  default := pure

instance {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] : Inhabited (m α) where
  default := pure default

-- A fusion of Haskell's `sequence` and `map`
def Array.sequenceMap {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (f : α → m β) : m (Array β) :=
  let rec loop (i : Nat) (j : Nat) (bs : Array β) : m (Array β) :=
    dite (LT.lt j as.size)
      (fun hlt =>
        match i with
        | 0           => pure bs
        | Nat.succ i' => Bind.bind (f (as.get ⟨j, hlt⟩)) fun b => loop i' (hAdd j 1) (bs.push b))
      (fun _ => pure bs)
  loop as.size 0 (Array.mkEmpty as.size)

/-- A Function for lifting a computation from an inner Monad to an outer Monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α

/-- The reflexive-transitive closure of `MonadLift`.
    `monadLift` is used to transitively lift monadic computations such as `StateT.get` or `StateT.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α

export MonadLiftT (monadLift)

abbrev liftM := @monadLift

instance (m n o) [MonadLift n o] [MonadLiftT m n] : MonadLiftT m o where
  monadLift x := MonadLift.monadLift (m := n) (monadLift x)

instance (m) : MonadLiftT m m where
  monadLift x := x

/-- A functor in the category of monads. Can be used to lift monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor). -/
class MonadFunctor (m : Type u → Type v) (n : Type u → Type w) where
  monadMap {α : Type u} : ({β : Type u} → m β → m β) → n α → n α

/-- The reflexive-transitive closure of `MonadFunctor`.
    `monadMap` is used to transitively lift Monad morphisms -/
class MonadFunctorT (m : Type u → Type v) (n : Type u → Type w) where
  monadMap {α : Type u} : ({β : Type u} → m β → m β) → n α → n α

export MonadFunctorT (monadMap)

instance (m n o) [MonadFunctor n o] [MonadFunctorT m n] : MonadFunctorT m o where
  monadMap f := MonadFunctor.monadMap (m := n) (monadMap (m := m) f)

instance monadFunctorRefl (m) : MonadFunctorT m m where
  monadMap f := f

inductive Except (ε : Type u) (α : Type v) where
  | error : ε → Except ε α
  | ok    : α → Except ε α

attribute [unbox] Except

instance {ε : Type u} {α : Type v} [Inhabited ε] : Inhabited (Except ε α) where
  default := Except.error default

/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class MonadExceptOf (ε : Type u) (m : Type v → Type w) where
  throw {α : Type v} : ε → m α
  tryCatch {α : Type v} : m α → (ε → m α) → m α

abbrev throwThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (e : ε) : m α :=
  MonadExceptOf.throw e

abbrev tryCatchThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (x : m α) (handle : ε → m α) : m α :=
  MonadExceptOf.tryCatch x handle

/-- Similar to `MonadExceptOf`, but `ε` is an outParam for convenience -/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw {α : Type v} : ε → m α
  tryCatch {α : Type v} : m α → (ε → m α) → m α

def MonadExcept.ofExcept [Monad m] [MonadExcept ε m] : Except ε α → m α
  | .ok a    => pure a
  | .error e => throw e

export MonadExcept (throw tryCatch ofExcept)

instance (ε : outParam (Type u)) (m : Type v → Type w) [MonadExceptOf ε m] : MonadExcept ε m where
  throw    := throwThe ε
  tryCatch := tryCatchThe ε

namespace MonadExcept
variable {ε : Type u} {m : Type v → Type w}

@[inline] protected def orElse [MonadExcept ε m] {α : Type v} (t₁ : m α) (t₂ : Unit → m α) : m α :=
  tryCatch t₁ fun _ => t₂ ()

instance [MonadExcept ε m] {α : Type v} : OrElse (m α) where
  orElse := MonadExcept.orElse

end MonadExcept

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α

instance (ρ : Type u) (m : Type u → Type v) (α : Type u) [Inhabited (m α)] : Inhabited (ReaderT ρ m α) where
  default := fun _ => default

@[inline] def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
  x r

namespace ReaderT

section
variable {ρ : Type u} {m : Type u → Type v} {α : Type u}

instance  : MonadLift m (ReaderT ρ m) where
  monadLift x := fun _ => x

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ReaderT ρ m) where
  throw e  := liftM (m := m) (throw e)
  tryCatch := fun x c r => tryCatchThe ε (x r) (fun e => (c e) r)

end

section
variable {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline] protected def read : ReaderT ρ m ρ :=
  pure

@[inline] protected def pure (a : α) : ReaderT ρ m α :=
  fun _ => pure a

@[inline] protected def bind (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) : ReaderT ρ m β :=
  fun r => bind (x r) fun a => f a r

@[inline] protected def map (f : α → β) (x : ReaderT ρ m α) : ReaderT ρ m β :=
  fun r => Functor.map f (x r)

instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
  map  := ReaderT.map

instance (ρ m) [Monad m] : MonadFunctor m (ReaderT ρ m) where
  monadMap f x := fun ctx => f (x ctx)

@[inline] protected def adapt {ρ' : Type u} [Monad m] {α : Type u} (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α :=
  fun x r => x (f r)

end
end ReaderT

/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this Function cannot be lifted using `monadLift`.
    Instead, the `MonadReaderAdapter` class provides the more general `adaptReader` Function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadReader (ρ : outParam (Type u)) (n : Type u → Type u) where
      lift {α : Type u} : ({m : Type u → Type u} → [Monad m] → ReaderT ρ m α) → n α
    ```
    -/
class MonadReaderOf (ρ : Type u) (m : Type u → Type v) where
  read : m ρ

@[inline] def readThe (ρ : Type u) {m : Type u → Type v} [MonadReaderOf ρ m] : m ρ :=
  MonadReaderOf.read

/-- Similar to `MonadReaderOf`, but `ρ` is an outParam for convenience -/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  read : m ρ

export MonadReader (read)

instance (ρ : Type u) (m : Type u → Type v) [MonadReaderOf ρ m] : MonadReader ρ m where
  read := readThe ρ

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n] [MonadReaderOf ρ m] : MonadReaderOf ρ n where
  read := liftM (m := m) read

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadReaderOf ρ (ReaderT ρ m) where
  read := ReaderT.read

class MonadWithReaderOf (ρ : Type u) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α

@[inline] def withTheReader (ρ : Type u) {m : Type u → Type v} [MonadWithReaderOf ρ m] {α : Type u} (f : ρ → ρ) (x : m α) : m α :=
  MonadWithReaderOf.withReader f x

class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α

export MonadWithReader (withReader)

instance (ρ : Type u) (m : Type u → Type v) [MonadWithReaderOf ρ m] : MonadWithReader ρ m where
  withReader := withTheReader ρ

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type v} [MonadFunctor m n] [MonadWithReaderOf ρ m] : MonadWithReaderOf ρ n where
  withReader f := monadMap (m := m) (withTheReader ρ f)

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadWithReaderOf ρ (ReaderT ρ m) where
  withReader f x := fun ctx => x (f ctx)

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monadLift`. -/
class MonadStateOf (σ : Type u) (m : Type u → Type v) where
  /-- Obtain the top-most State of a Monad stack. -/
  get : m σ
  /-- Set the top-most State of a Monad stack. -/
  set : σ → m PUnit
  /-- Map the top-most State of a Monad stack.

  Note: `modifyGet f` may be preferable to `do s <- get; let (a, s) := f s; put s; pure a`
  because the latter does not use the State linearly (without sufficient inlining). -/
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

export MonadStateOf (set)

abbrev getThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] : m σ :=
  MonadStateOf.get

@[inline] abbrev modifyThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → σ) : m PUnit :=
  MonadStateOf.modifyGet fun s => (PUnit.unit, f s)

@[inline] abbrev modifyGetThe {α : Type u} (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → Prod α σ) : m α :=
  MonadStateOf.modifyGet f

/-- Similar to `MonadStateOf`, but `σ` is an outParam for convenience -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) where
  get : m σ
  set : σ → m PUnit
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

export MonadState (get modifyGet)

instance (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] : MonadState σ m where
  set         := MonadStateOf.set
  get         := getThe σ
  modifyGet f := MonadStateOf.modifyGet f

@[inline] def modify {σ : Type u} {m : Type u → Type v} [MonadState σ m] (f : σ → σ) : m PUnit :=
  modifyGet fun s => (PUnit.unit, f s)

@[inline] def getModify {σ : Type u} {m : Type u → Type v} [MonadState σ m] [Monad m] (f : σ → σ) : m σ :=
  modifyGet fun s => (s, f s)

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
instance {σ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n] [MonadStateOf σ m] : MonadStateOf σ n where
  get         := liftM (m := m) MonadStateOf.get
  set       s := liftM (m := m) (MonadStateOf.set s)
  modifyGet f := monadLift (m := m) (MonadState.modifyGet f)

namespace EStateM

inductive Result (ε σ α : Type u) where
  | ok    : α → σ → Result ε σ α
  | error : ε → σ → Result ε σ α

variable {ε σ α : Type u}

instance [Inhabited ε] [Inhabited σ] : Inhabited (Result ε σ α) where
  default := Result.error default default

end EStateM

open EStateM (Result) in
def EStateM (ε σ α : Type u) := σ → Result ε σ α

namespace EStateM

variable {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EStateM ε σ α) where
  default := fun s => Result.error default s

@[inline] protected def pure (a : α) : EStateM ε σ α := fun s =>
  Result.ok a s

@[inline] protected def set (s : σ) : EStateM ε σ PUnit := fun _ =>
  Result.ok ⟨⟩ s

@[inline] protected def get : EStateM ε σ σ := fun s =>
  Result.ok s s

@[inline] protected def modifyGet (f : σ → Prod α σ) : EStateM ε σ α := fun s =>
  match f s with
  | (a, s) => Result.ok a s

@[inline] protected def throw (e : ε) : EStateM ε σ α := fun s =>
  Result.error e s

/-- Auxiliary instance for saving/restoring the "backtrackable" part of the state. -/
class Backtrackable (δ : outParam (Type u)) (σ : Type u) where
  save    : σ → δ
  restore : σ → δ → σ

@[inline] protected def tryCatch {δ} [Backtrackable δ σ] {α} (x : EStateM ε σ α) (handle : ε → EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s
  match x s with
  | Result.error e s => handle e (Backtrackable.restore s d)
  | ok               => ok

@[inline] protected def orElse {δ} [Backtrackable δ σ] (x₁ : EStateM ε σ α) (x₂ : Unit → EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error _ s => x₂ () (Backtrackable.restore s d)
  | ok               => ok

@[inline] def adaptExcept {ε' : Type u} (f : ε → ε') (x : EStateM ε σ α) : EStateM ε' σ α := fun s =>
  match x s with
  | Result.error e s => Result.error (f e) s
  | Result.ok a s    => Result.ok a s

@[inline] protected def bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => f a s
  | Result.error e s => Result.error e s

@[inline] protected def map (f : α → β) (x : EStateM ε σ α) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

@[inline] protected def seqRight (x : EStateM ε σ α) (y : Unit → EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok _ s    => y () s
  | Result.error e s => Result.error e s

instance : Monad (EStateM ε σ) where
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

@[inline] def run (x : EStateM ε σ α) (s : σ) : Result ε σ α :=
  x s

@[inline] def run' (x : EStateM ε σ α) (s : σ) : Option α :=
  match run x s with
  | Result.ok v _   => some v
  | Result.error .. => none

@[inline] def dummySave : σ → PUnit := fun _ => ⟨⟩

@[inline] def dummyRestore : σ → PUnit → σ := fun s _ => s

/-- Dummy default instance -/
instance nonBacktrackable : Backtrackable PUnit σ where
  save    := dummySave
  restore := dummyRestore

end EStateM

class Hashable (α : Sort u) where
  hash : α → UInt64

export Hashable (hash)

@[extern "lean_uint64_to_usize"]
opaque UInt64.toUSize (u : UInt64) : USize

@[extern "lean_usize_to_uint64"]
opaque USize.toUInt64 (u : USize) : UInt64

@[extern "lean_uint64_mix_hash"]
opaque mixHash (u₁ u₂ : UInt64) : UInt64

@[extern "lean_string_hash"]
protected opaque String.hash (s : @& String) : UInt64

instance : Hashable String where
  hash := String.hash

namespace Lean

/--
Hierarchical names. We use hierarchical names to name declarations and
for creating unique identifiers for free variables and metavariables.

You can create hierarchical names using the following quotation notation.
```
`Lean.Meta.whnf
```
It is short for `.str (.str (.str .anonymous "Lean") "Meta") "whnf"`
You can use double quotes to request Lean to statically check whether the name
corresponds to a Lean declaration in scope.
```
``Lean.Meta.whnf
```
If the name is not in scope, Lean will report an error.
-/
inductive Name where
  | /-- The "anonymous" name. -/
    anonymous : Name
  | /--
A string name. The name `Lean.Meta.run` is represented at
```lean
.str (.str (.str .anonymous "Lean") "Meta") "run"
```
-/
    str (pre : Name) (str : String)
  | /--
A numerical name. This kind of name is used, for example, to create hierarchical names for
free variables and metavariables. The identifier `_uniq.231` is represented as
```lean
.num (.str .anonymous "_uniq") 231
```
-/
    num (pre : Name) (i : Nat)
with
  @[computedField] hash : Name → UInt64
    | .anonymous => .ofNatCore 1723 (by decide)
    | .str p s => mixHash p.hash s.hash
    | .num p v => mixHash p.hash (dite (LT.lt v UInt64.size) (fun h => UInt64.ofNatCore v h) (fun _ => UInt64.ofNatCore 17 (by decide)))

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
Short for `.str .anonymous s`.
-/
abbrev mkSimple (s : String) : Name :=
  mkStr Name.anonymous s

@[extern "lean_name_eq"]
protected def beq : (@& Name) → (@& Name) → Bool
  | anonymous, anonymous => true
  | str p₁ s₁, str p₂ s₂ => and (BEq.beq s₁ s₂) (Name.beq p₁ p₂)
  | num p₁ n₁, num p₂ n₂ => and (BEq.beq n₁ n₂) (Name.beq p₁ p₂)
  | _,         _         => false

instance : BEq Name where
  beq := Name.beq

/--
Append two hierarchical names. Example:
```lean
`Lean.Meta ++ `Tactic.simp
```
return `Lean.Meta.Tactic.simp`
-/
protected def append : Name → Name → Name
  | n, anonymous => n
  | n, str p s => Name.mkStr (Name.append n p) s
  | n, num p d => Name.mkNum (Name.append n p) d

instance : Append Name where
  append := Name.append

end Name

/-! # Syntax -/

/-- Source information of tokens. -/
inductive SourceInfo where
  | /--
    Token from original input with whitespace and position information.
    `leading` will be inferred after parsing by `Syntax.updateLeading`. During parsing,
    it is not at all clear what the preceding token was, especially with backtracking.
    -/
   original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos)
  | /--
    Synthesized token (e.g. from a quotation) annotated with a span from the original source.
    In the delaborator, we "misuse" this constructor to store synthetic positions identifying
    subterms.
    -/
    synthetic (pos : String.Pos) (endPos : String.Pos)
  | /--
    Synthesized token without position information.
    -/
    protected none

instance : Inhabited SourceInfo := ⟨SourceInfo.none⟩

namespace SourceInfo

def getPos? (info : SourceInfo) (originalOnly := false) : Option String.Pos :=
  match info, originalOnly with
  | original (pos := pos) ..,  _     => some pos
  | synthetic (pos := pos) .., false => some pos
  | _,                         _     => none

end SourceInfo

abbrev SyntaxNodeKind := Name

/-! # Syntax AST -/

/--
Syntax objects used by the parser, macro expander, delaborator, etc.
-/
inductive Syntax where
  | missing : Syntax
  | /--
    Node in the syntax tree.

    The `info` field is used by the delaborator
    to store the position of the subexpression
    corresponding to this node.
    The parser sets the `info` field to `none`.

    (Remark: the `node` constructor
    did not have an `info` field in previous versions.
    This caused a bug in the interactive widgets,
    where the popup for `a + b` was the same as for `a`.
    The delaborator used to associate subexpressions
    with pretty-printed syntax by setting
    the (string) position of the first atom/identifier
    to the (expression) position of the subexpression.
    For example, both `a` and `a + b`
    have the same first identifier,
    and so their infos got mixed up.)
    -/
    node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom   (info : SourceInfo) (val : String) : Syntax
  | ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Prod Name (List String))) : Syntax

def SyntaxNodeKinds := List SyntaxNodeKind

/--
A `Syntax` value of one of the given syntax kinds.
Note that while syntax quotations produce/expect `TSyntax` values of the correct kinds,
this is not otherwise enforced and can easily be circumvented by direct use of the constructor.
The namespace `TSyntax.Compat` can be opened to expose a general coercion from `Syntax` to any
`TSyntax ks` for porting older code. -/
structure TSyntax (ks : SyntaxNodeKinds) where
  raw : Syntax

instance : Inhabited Syntax where
  default := Syntax.missing

instance : Inhabited (TSyntax ks) where
  default := ⟨default⟩

/-! Builtin kinds -/
abbrev choiceKind : SyntaxNodeKind := `choice
abbrev nullKind : SyntaxNodeKind := `null
abbrev groupKind : SyntaxNodeKind := `group
abbrev identKind : SyntaxNodeKind := `ident
abbrev strLitKind : SyntaxNodeKind := `str
abbrev charLitKind : SyntaxNodeKind := `char
abbrev numLitKind : SyntaxNodeKind := `num
abbrev scientificLitKind : SyntaxNodeKind := `scientific
abbrev nameLitKind : SyntaxNodeKind := `name
abbrev fieldIdxKind : SyntaxNodeKind := `fieldIdx
abbrev interpolatedStrLitKind : SyntaxNodeKind := `interpolatedStrLitKind
abbrev interpolatedStrKind : SyntaxNodeKind := `interpolatedStrKind

namespace Syntax

def getKind (stx : Syntax) : SyntaxNodeKind :=
  match stx with
  | Syntax.node _ k _    => k
  -- We use these "pseudo kinds" for antiquotation kinds.
  -- For example, an antiquotation `$id:ident` (using Lean.Parser.Term.ident)
  -- is compiled to ``if stx.isOfKind `ident ...``
  | Syntax.missing     => `missing
  | Syntax.atom _ v    => Name.mkSimple v
  | Syntax.ident ..    => identKind

def setKind (stx : Syntax) (k : SyntaxNodeKind) : Syntax :=
  match stx with
  | Syntax.node info _ args => Syntax.node info k args
  | _                       => stx

def isOfKind (stx : Syntax) (k : SyntaxNodeKind) : Bool :=
  beq stx.getKind k

def getArg (stx : Syntax) (i : Nat) : Syntax :=
  match stx with
  | Syntax.node _ _ args => args.getD i Syntax.missing
  | _                    => Syntax.missing

instance : GetElem Syntax Nat Syntax fun _ _ => True where
  getElem stx i _ := stx.getArg i

def getArgs (stx : Syntax) : Array Syntax :=
  match stx with
  | Syntax.node _ _ args => args
  | _                    => Array.empty

def getNumArgs (stx : Syntax) : Nat :=
  match stx with
  | Syntax.node _ _ args => args.size
  | _                    => 0

def getOptional? (stx : Syntax) : Option Syntax :=
  match stx with
  | Syntax.node _ k args => match and (beq k nullKind) (beq args.size 1) with
    | true  => some (args.get! 0)
    | false => none
  | _                    => none

def isMissing : Syntax → Bool
  | Syntax.missing => true
  | _ => false

def isNodeOf (stx : Syntax) (k : SyntaxNodeKind) (n : Nat) : Bool :=
  and (stx.isOfKind k) (beq stx.getNumArgs n)

/-- `stx.isIdent` is `true` iff `stx` is an identifier. -/
def isIdent : Syntax → Bool
  | ident .. => true
  | _        => false

def getId : Syntax → Name
  | ident _ _ val _ => val
  | _               => Name.anonymous

def setArgs (stx : Syntax) (args : Array Syntax) : Syntax :=
  match stx with
  | node info k _ => node info k args
  | stx           => stx

def setArg (stx : Syntax) (i : Nat) (arg : Syntax) : Syntax :=
  match stx with
  | node info k args => node info k (args.setD i arg)
  | stx              => stx

/-- Retrieve the left-most node or leaf's info in the Syntax tree. -/
partial def getHeadInfo? : Syntax → Option SourceInfo
  | atom info _   => some info
  | ident info .. => some info
  | node SourceInfo.none _ args   =>
    let rec loop (i : Nat) : Option SourceInfo :=
      match decide (LT.lt i args.size) with
      | true => match getHeadInfo? (args.get! i) with
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

def getPos? (stx : Syntax) (originalOnly := false) : Option String.Pos :=
  stx.getHeadInfo.getPos? originalOnly

partial def getTailPos? (stx : Syntax) (originalOnly := false) : Option String.Pos :=
  match stx, originalOnly with
  | atom (SourceInfo.original (endPos := pos) ..) ..,    _    => some pos
  | atom (SourceInfo.synthetic (endPos := pos) ..) _,  false  => some pos
  | ident (SourceInfo.original (endPos := pos) ..) .., _      => some pos
  | ident (SourceInfo.synthetic (endPos := pos) ..) .., false => some pos
  | node (SourceInfo.original (endPos := pos) ..) ..,    _    => some pos
  | node (SourceInfo.synthetic (endPos := pos) ..) .., false  => some pos
  | node _ _ args,                                        _     =>
    let rec loop (i : Nat) : Option String.Pos :=
      match decide (LT.lt i args.size) with
      | true => match getTailPos? (args.get! ((args.size.sub i).sub 1)) originalOnly with
         | some info => some info
         | none      => loop (hAdd i 1)
      | false => none
    loop 0
  | _, _ => none

/--
  An array of syntax elements interspersed with separators. Can be coerced to/from `Array Syntax` to automatically
  remove/insert the separators. -/
structure SepArray (sep : String) where
  elemsAndSeps : Array Syntax

/-- A typed version of `SepArray`. -/
structure TSepArray (ks : SyntaxNodeKinds) (sep : String) where
  elemsAndSeps : Array Syntax

end Syntax

abbrev TSyntaxArray (ks : SyntaxNodeKinds) := Array (TSyntax ks)

unsafe def TSyntaxArray.rawImpl : TSyntaxArray ks → Array Syntax := unsafeCast

@[implementedBy TSyntaxArray.rawImpl]
opaque TSyntaxArray.raw (as : TSyntaxArray ks) : Array Syntax := Array.empty

unsafe def TSyntaxArray.mkImpl : Array Syntax → TSyntaxArray ks := unsafeCast

@[implementedBy TSyntaxArray.mkImpl]
opaque TSyntaxArray.mk (as : Array Syntax) : TSyntaxArray ks := Array.empty

def SourceInfo.fromRef (ref : Syntax) : SourceInfo :=
  match ref.getPos?, ref.getTailPos? with
  | some pos, some tailPos => SourceInfo.synthetic pos tailPos
  | _,        _            => SourceInfo.none

def mkAtom (val : String) : Syntax :=
  Syntax.atom SourceInfo.none val

def mkAtomFrom (src : Syntax) (val : String) : Syntax :=
  Syntax.atom (SourceInfo.fromRef src) val

/-! # Parser descriptions -/

inductive ParserDescr where
  | const  (name : Name)
  | unary  (name : Name) (p : ParserDescr)
  | binary (name : Name) (p₁ p₂ : ParserDescr)
  | node (kind : SyntaxNodeKind) (prec : Nat) (p : ParserDescr)
  | trailingNode (kind : SyntaxNodeKind) (prec lhsPrec : Nat) (p : ParserDescr)
  | symbol (val : String)
  | nonReservedSymbol (val : String) (includeIdent : Bool)
  | cat (catName : Name) (rbp : Nat)
  | parser (declName : Name)
  | nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : ParserDescr)
  | sepBy  (p : ParserDescr) (sep : String) (psep : ParserDescr) (allowTrailingSep : Bool := false)
  | sepBy1 (p : ParserDescr) (sep : String) (psep : ParserDescr) (allowTrailingSep : Bool := false)

instance : Inhabited ParserDescr where
  default := ParserDescr.symbol ""

abbrev TrailingParserDescr := ParserDescr

/-!
Runtime support for making quotation terms auto-hygienic, by mangling identifiers
introduced by them with a "macro scope" supplied by the context. Details to appear in a
paper soon.
-/

abbrev MacroScope := Nat
/-- Macro scope used internally. It is not available for our frontend. -/
def reservedMacroScope := 0
/-- First macro scope available for our frontend -/
def firstFrontendMacroScope := hAdd reservedMacroScope 1

class MonadRef (m : Type → Type) where
  getRef      : m Syntax
  withRef {α} : Syntax → m α → m α

export MonadRef (getRef)

instance (m n : Type → Type) [MonadLift m n] [MonadFunctor m n] [MonadRef m] : MonadRef n where
  getRef        := liftM (getRef : m _)
  withRef ref x := monadMap (m := m) (MonadRef.withRef ref) x

def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
  match ref.getPos? with
  | some _ => ref
  | _      => oldRef

@[inline] def withRef {m : Type → Type} [Monad m] [MonadRef m] {α} (ref : Syntax) (x : m α) : m α :=
  bind getRef fun oldRef =>
  let ref := replaceRef ref oldRef
  MonadRef.withRef ref x

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
     scope before the recursive call is restored after it, as expected. -/
  withFreshMacroScope {α : Type} : m α → m α

export MonadQuotation (getCurrMacroScope getMainModule withFreshMacroScope)

def MonadRef.mkInfoFromRefPos [Monad m] [MonadRef m] : m SourceInfo :=
  return SourceInfo.fromRef (← getRef)

instance {m n : Type → Type} [MonadFunctor m n] [MonadLift m n] [MonadQuotation m] : MonadQuotation n where
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
The main modules being processed is always the right most one.
This situation may happen when we execute a macro generated in
an imported file in the current file.
```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```

The delimiter `_hyg` is used just to improve the `hasMacroScopes` performance.
-/

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

structure MacroScopesView where
  name       : Name
  imported   : Name
  mainModule : Name
  scopes     : List MacroScope

instance : Inhabited MacroScopesView where
  default := ⟨default, default, default, default⟩

def MacroScopesView.review (view : MacroScopesView) : Name :=
  match view.scopes with
  | List.nil      => view.name
  | List.cons _ _ =>
    let base := (Name.mkStr (hAppend (hAppend (Name.mkStr view.name "_@") view.imported) view.mainModule) "_hyg")
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

def addMacroScope (mainModule : Name) (n : Name) (scp : MacroScope) : Name :=
  match n.hasMacroScopes with
  | true =>
    let view := extractMacroScopes n
    match beq view.mainModule mainModule with
    | true  => Name.mkNum n scp
    | false =>
      { view with
        imported   := view.scopes.foldl Name.mkNum (hAppend view.imported view.mainModule)
        mainModule := mainModule
        scopes     := List.cons scp List.nil
      }.review
  | false =>
    Name.mkNum (Name.mkStr (hAppend (Name.mkStr n "_@") mainModule) "_hyg") scp

@[inline] def MonadQuotation.addMacroScope {m : Type → Type} [MonadQuotation m] [Monad m] (n : Name) : m Name :=
  bind getMainModule     fun mainModule =>
  bind getCurrMacroScope fun scp =>
  pure (Lean.addMacroScope mainModule n scp)

def defaultMaxRecDepth := 512

def maxRecDepthErrorMessage : String :=
  "maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)"

namespace Syntax

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

structure Context where
  methods        : MethodsRef
  mainModule     : Name
  currMacroScope : MacroScope
  currRecDepth   : Nat := 0
  maxRecDepth    : Nat := defaultMaxRecDepth
  ref            : Syntax

inductive Exception where
  | error             : Syntax → String → Exception
  | unsupportedSyntax : Exception

structure State where
  macroScope : MacroScope
  traceMsgs  : List (Prod Name String) := List.nil
  deriving Inhabited

end Macro

abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception Macro.State)

abbrev Macro := Syntax → MacroM Syntax

namespace Macro

instance : MonadRef MacroM where
  getRef     := bind read fun ctx => pure ctx.ref
  withRef    := fun ref x => withReader (fun ctx => { ctx with ref := ref }) x

def addMacroScope (n : Name) : MacroM Name :=
  bind read fun ctx =>
  pure (Lean.addMacroScope ctx.mainModule n ctx.currMacroScope)

def throwUnsupported {α} : MacroM α :=
  throw Exception.unsupportedSyntax

def throwError {α} (msg : String) : MacroM α :=
  bind getRef fun ref =>
  throw (Exception.error ref msg)

def throwErrorAt {α} (ref : Syntax) (msg : String) : MacroM α :=
  withRef ref (throwError msg)

@[inline] protected def withFreshMacroScope {α} (x : MacroM α) : MacroM α :=
  bind (modifyGet (fun s => (s.macroScope, { s with macroScope := hAdd s.macroScope 1 }))) fun fresh =>
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

@[inline] def withIncRecDepth {α} (ref : Syntax) (x : MacroM α) : MacroM α :=
  bind read fun ctx =>
  match beq ctx.currRecDepth ctx.maxRecDepth with
  | true  => throw (Exception.error ref maxRecDepthErrorMessage)
  | false => withReader (fun ctx => { ctx with currRecDepth := hAdd ctx.currRecDepth 1 }) x

instance : MonadQuotation MacroM where
  getCurrMacroScope ctx := pure ctx.currMacroScope
  getMainModule     ctx := pure ctx.mainModule
  withFreshMacroScope   := Macro.withFreshMacroScope

structure Methods where
  expandMacro?      : Syntax → MacroM (Option Syntax)
  getCurrNamespace  : MacroM Name
  hasDecl           : Name → MacroM Bool
  resolveNamespace  : Name → MacroM (List Name)
  resolveGlobalName : Name → MacroM (List (Prod Name (List String)))
  deriving Inhabited

unsafe def mkMethodsImp (methods : Methods) : MethodsRef :=
  unsafeCast methods

@[implementedBy mkMethodsImp]
opaque mkMethods (methods : Methods) : MethodsRef

instance : Inhabited MethodsRef where
  default := mkMethods default

unsafe def getMethodsImp : MacroM Methods :=
  bind read fun ctx => pure (unsafeCast (ctx.methods))

@[implementedBy getMethodsImp] opaque getMethods : MacroM Methods

/-- `expandMacro? stx` return `some stxNew` if `stx` is a macro, and `stxNew` is its expansion. -/
def expandMacro? (stx : Syntax) : MacroM (Option Syntax) := do
  (← getMethods).expandMacro? stx

/-- Return `true` if the environment contains a declaration with name `declName` -/
def hasDecl (declName : Name) : MacroM Bool := do
  (← getMethods).hasDecl declName

def getCurrNamespace : MacroM Name := do
  (← getMethods).getCurrNamespace

def resolveNamespace (n : Name) : MacroM (List Name) := do
  (← getMethods).resolveNamespace n

def resolveGlobalName (n : Name) : MacroM (List (Prod Name (List String))) := do
  (← getMethods).resolveGlobalName n

def trace (clsName : Name) (msg : String) : MacroM Unit := do
  modify fun s => { s with traceMsgs := List.cons (Prod.mk clsName msg) s.traceMsgs }

end Macro

export Macro (expandMacro?)

namespace PrettyPrinter

abbrev UnexpandM := ReaderT Syntax (EStateM Unit Unit)

/--
  Function that tries to reverse macro expansions as a post-processing step of delaboration.
  While less general than an arbitrary delaborator, it can be declared without importing `Lean`.
  Used by the `[appUnexpander]` attribute. -/
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
