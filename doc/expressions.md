Expressions
===========

Every expression in Lean has a [Type](types.md). Every type is also an
expression of type `Sort u` for some universe level u. See [Type
Universes](types.md#type_universes).

Expression Syntax
=================

The set of expressions in Lean is defined inductively as follows:

* ``Sort u`` : the universe of types at universe level ``u``
* ``c`` : where ``c`` is an identifier denoting a declared constant or a defined object
* ``x`` : where ``x`` is a variable in the local context in which the expression is interpreted
* `m?`  : where `m?` is a metavariable in the metavariable context in which the expression is interpreted,
  you can view metavariable as a "hole" that still needs to be synthesized
* ``(x : α) → β`` : the type of functions taking an element ``x`` of ``α`` to an element of ``β``,
  where ``β`` is an expression whose type is a ``Sort``
* ``s t`` : the result of applying ``s`` to ``t``, where ``s`` and ``t`` are expressions
* ``fun x : α => t`` or `λ x : α => t`: the function mapping any value ``x`` of type ``α`` to ``t``, where ``t`` is an expression
* ``let x := t; s`` : a local definition, denotes the value of ``s`` when ``x`` is replaced by ``t``
* `s.i`   : a projection, denotes the value of the `i`-th field of `s`
* `lit`   : a natural number or string literal
* `mdata k s` : the expression `s` decorated with metadata `k`, where is a key-value map

Every well formed term in Lean has a *type*, which itself is an expression of type ``Sort u`` for some ``u``. The fact that a term ``t`` has type ``α`` is written ``t : α``.

For an expression to be well formed, its components have to satisfy certain typing constraints. These, in turn, determine the type of the resulting term, as follows:

* ``Sort u : Sort (u + 1)``
* ``c : α``, where ``α`` is the type that ``c`` has been declared or defined to have
* ``x : α``, where ``α`` is the type that ``x`` has been assigned in the local context where it is interpreted
* ``?m : α``, where ``α`` is the type that ``?m`` has been declared in the metavariable context where it is interpreted
* ``(x : α) → β : Sort (imax u v)`` where ``α : Sort u``, and ``β : Sort v`` assuming ``x : α``
* ``s t : β[t/x]`` where ``s`` has type ``(x : α) → β`` and ``t`` has type ``α``
* ``(fun x : α => t) : (x : α) → β`` if ``t`` has type ``β`` whenever ``x`` has type ``α``
* ``(let x := t; s) : β[t/x]`` where ``t`` has type ``α`` and ``s`` has type ``β`` assuming ``x : α``
* `lit : Nat` if `lit` is a numeral
* `lit : String` if `lit` is a string literal
* `mdata k s : α` if `s : α`
* `s.i : α` if `s : β` and `β` is an inductive datatype with only one constructor, and `i`-th field has type `α`

``Prop`` abbreviates ``Sort 0``, ``Type`` abbreviates ``Sort 1``, and
``Type u`` abbreviates ``Sort (u + 1)`` when ``u`` is a universe
variable. We say "``α`` is a type" to express ``α : Type u`` for some
``u``, and we say "``p`` is a proposition" to express
``p : Prop``. Using the *propositions as types* correspondence, given
``p : Prop``, we refer to an expression ``t : p`` as a *proof* of ``p``. In
contrast, given ``α : Type u`` for some ``u`` and ``t : α``, we
sometimes refer to ``t`` as *data*.

When the expression ``β`` in ``(x : α) → β`` does not depend on ``x``,
it can be written ``α → β``. As usual, the variable ``x`` is bound in
``(x : α) →  β``, ``fun x : α => t``, and ``let x := t; s``. The
expression ``∀ x : α, β`` is alternative syntax for ``(x : α) →  β``,
and is intended to be used when ``β`` is a proposition. An underscore
can be used to generate an internal variable in a binder, as in
``fun _ : α => t``.

*Metavariables*, that is, temporary placeholders, are used in the
process of constructing terms. Terms that are added to the
environment contain neither metavariable nor variables, which is to
say, they are fully elaborated and make sense in the empty context.

Axioms can be declared using the ``axiom`` keyword.
Similarly, objects can be defined in various ways, such as using ``def`` and ``theorem`` keywords.
See [Chapter Declarations](./declarations.md) for more information.

Writing an expression ``(t : α)`` forces Lean to elaborate ``t`` so that it has type ``α`` or report an error if it fails.

Lean supports anonymous constructor notation, anonymous projections,
and various forms of match syntax, including destructuring ``fun`` and
``let``. These, as well as notation for common data types (like pairs,
lists, and so on) are discussed in [Chapter Declarations](./declarations.md)
in connection with inductive types.

```lean
universe u

#check Sort 0
#check Prop
#check Sort 1
#check Type
#check Sort u
#check Sort (u+1)

#check Nat → Bool
#check (α : Type u) → List α
#check (α : Type u) → (β : Type u) → Sum α β
#check fun x : Nat => x
#check fun (α : Type u) (x : α) => x
#check let x := 5; x * 2
#check "hello"
#check (fun x => x) true
```

Implicit Arguments
==================

When declaring arguments to defined objects in Lean (for example, with
``def``, ``theorem``, ``axiom``, ``constant``, ``inductive``, or
``structure``; see [Chapter Declarations](./declarations.md) or when
declaring variables in sections (see [Other Commands](./other_commands.md)),
arguments can be annotated as *explicit* or *implicit*.
This determines how expressions containing the object are interpreted.

* ``(x : α)`` : an explicit argument of type ``α``
* ``{x : α}`` : an implicit argument, eagerly inserted
* ``⦃x : α⦄`` or ``{{x : α}}`` : an implicit argument, weakly inserted
* ``[x : α]`` : an implicit argument that should be inferred by type class resolution
* ``(x : α := v)`` : an optional argument, with default value ``v``
* ``(x : α := by tac)`` : an implicit argument, to be synthesized by tactic ``tac``

The name of the variable can be omitted from a class resolution
argument, in which case an internal name is generated.

When a function has an explicit argument, you can nonetheless ask
Lean's elaborator to infer the argument automatically, by entering it
as an underscore (``_``). Conversely, writing ``@foo`` indicates that
all of the arguments to be ``foo`` are to be given explicitly,
independent of how ``foo`` was declared.  You can also provide a value
for an implicit parameter using named arguments.  Named arguments
enable you to specify an argument for a parameter by matching the
argument with its name rather than with its position in the parameter
list.  If you don't remember the order of the parameters but know
their names, you can send the arguments in any order.  You may also
provide the value for an implicit parameter whenLean failed to infer
it. Named arguments also improve the readability of your code by
identifying what each argument represents.


```lean
def add (x y : Nat) : Nat :=
  x + y

#check add 2 3 -- Nat
#eval add 2 3  -- 5

def id1 (α : Type u) (x : α) : α := x

#check id1 Nat 3
#check id1 _ 3

def id2 {α : Type u} (x : α) : α := x

#check id2 3
#check @id2 Nat 3
#check id2 (α := Nat) 3
#check id2
#check id2 (α := Nat)

def id3 {{α : Type u}} (x : α) : α := x

#check id3 3
#check @id3 Nat 3
#check (id3 : (α : Type) → α → α)

class Cls where
  val : Nat

instance Cls_five : Cls where
  val := 5

def ex2 [c : Cls] : Nat := c.val

example : ex2 = 5 := rfl

def ex2a [Cls] : Nat := ex2

example : ex2a = 5 := rfl

def ex3 (x : Nat := 5) := x

#check ex3 2
#check ex3

example : ex3 = 5 := rfl

def ex4 (x : Nat) (y : Nat := x) : Nat :=
  x * y

example : ex4 x = x * x :=
  rfl
```

Basic Data Types and Assertions
===============================

The core library contains a number of basic data types, such as the
natural numbers (`Nat`), the integers (`Int`), the
booleans (``Bool``), and common operations on these, as well as the
usual logical quantifiers and connectives. Some example are given
below. A list of common notations and their precedences can be found
in a [file](https://github.com/leanprover/lean4/blob/master/src/Init/Notation.lean)
in the core library. The core library also contains a number of basic
data type constructors. Definitions can also be found the
[Data](https://github.com/leanprover/lean4/blob/master/src/Init/Data)
directory of the core library. For more information, see also [Chapter libraries](./libraries.md).

```
/- numbers -/
def f1 (a b c : Nat) : Nat :=
  a^2 + b^2 + c^2

def p1 (a b c d : Nat) : Prop :=
  (a + b)^c ≤ d

def p2 (i j k : Int) : Prop :=
  i % (j * k) = 0


/- booleans -/

def f2 (a b c : Bool) : Bool :=
  a && (b || c)

/- pairs -/

#eval (1, 2)

def p : Nat × Bool := (1, false)

section
variable (a b c : Nat) (p : Nat × bool)

#check (1, 2)
#check p.1 * 2
#check p.2 && tt
#check ((1, 2, 3) : Nat × Nat × Nat)
end

/- lists -/
section
variable x y z : Nat
variable xs ys zs : list Nat
open list

#check (1 :: xs) ++ (y :: zs) ++ [1,2,3]
#check append (cons 1 xs) (cons y zs)
#check map (λ x, x^2) [1, 2, 3]
end

/- sets -/
section
variable s t u : set Nat

#check ({1, 2, 3} ∩ s) ∪ ({x | x < 7} ∩ t)
end

/- strings and characters -/
#check "hello world"
#check 'a'

/- assertions -/
#check ∀ a b c n : Nat,
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ n > 2 → a^n + b^n ≠ c^n

def unbounded (f : Nat → Nat) : Prop := ∀ M, ∃ n, f n ≥ M
```
.. _constructors_projections_and_matching:

Constructors, Projections, and Matching
=======================================

Lean's foundation, the *Calculus of Inductive Constructions*, supports the declaration of *inductive types*. Such types can have any number of *constructors*, and an associated *eliminator* (or *recursor*). Inductive types with one constructor, known as *structures*, have *projections*. The full syntax of inductive types is described in [Declarations](declarations.md), but here we describe some syntactic elements that facilitate their use in expressions.

When Lean can infer the type of an expression and it is an inductive type with one constructor, then one can write ``⟨a1, a2, ..., an⟩`` to apply the constructor without naming it. For example, ``⟨a, b⟩`` denotes ``prod.mk a b`` in a context where the expression can be inferred to be a pair, and ``⟨h₁, h₂⟩`` denotes ``and.intro h₁ h₂`` in a context when the expression can be inferred to be a conjunction. The notation will nest constructions automatically, so ``⟨a1, a2, a3⟩`` is interpreted as ``prod.mk a1 (prod.mk a2 a3)`` when the expression is expected to have a type of the form ``α1 × α2 × α3``. (The latter is interpreted as ``α1 × (α2 × α3)``, since the product associates to the right.)

Similarly, one can use "dot notation" for projections: one can write ``p.fst`` and ``p.snd`` for ``prod.fst p`` and ``prod.snd p`` when Lean can infer that ``p`` is an element of a product, and ``h.left`` and ``h.right`` for ``and.left h`` and ``and.right h`` when ``h`` is a conjunction.

The anonymous projector notation can used more generally for any objects defined in a *namespace* (see [Other Commands](other_commands.md)). For example, if ``l`` has type ``list α`` then ``l.map f`` abbreviates ``list.map f l``, in which ``l`` has been placed at the first argument position where ``list.map`` expects a ``list``.

Finally, for data types with one constructor, one destruct an element by pattern matching using the ``let`` and ``assume`` constructs, as in the examples below. Internally, these are interpreted using the ``match`` construct, which is in turn compiled down for the eliminator for the inductive type, as described in [Declarations](declarations.md).

.. code-block:: lean

    universes u v
    variable {α : Type u} {β : Type v}

    def p : Nat × ℤ := ⟨1, 2⟩
    #check p.fst
    #check p.snd

    def p' : Nat × ℤ × bool := ⟨1, 2, tt⟩
    #check p'.fst
    #check p'.snd.fst
    #check p'.snd.snd

    def swap_pair (p : α × β) : β × α :=
    ⟨p.snd, p.fst⟩

    theorem swap_conj {a b : Prop} (h : a ∧ b) : b ∧ a :=
    ⟨h.right, h.left⟩

    #check [1, 2, 3].append [2, 3, 4]
    #check [1, 2, 3].map (λ x, x^2)

    example (p q : Prop) : p ∧ q → q ∧ p :=
    λ h, ⟨h.right, h.left⟩

    def swap_pair' (p : α × β) : β × α :=
    let (x, y) := p in (y, x)

    theorem swap_conj' {a b : Prop} (h : a ∧ b) : b ∧ a :=
    let ⟨ha, hb⟩ := h in ⟨hb, ha⟩

    def swap_pair'' : α × β → β × α :=
    λ ⟨x, y⟩, (y, x)

    theorem swap_conj'' {a b : Prop} : a ∧ b → b ∧ a :=
    assume ⟨ha, hb⟩, ⟨hb, ha⟩

Structured Proofs
=================

Syntactic sugar is provided for writing structured proof terms:

* ``have h : p := s; t`` is sugar for ``(fun h : p => t) s``
* ``suffices h : p from s; t`` is sugar for ``(λ h : p => s) t``
* ``suffices h : p by s; t`` is sugar for ``(suffixes h : p from by s; t)``
* ``show p from t`` is sugar for ``(have this : p := t; this)``
* ``show p by tac`` is sugar for ``(show p from by tac)``

Types can be omitted when they can be inferred by Lean. Lean also
allows ``have : p := t; s``, which gives the assumption the
name ``this`` in the local context.  Similarly, Lean recognizes the
variant ``suffices p from s; t``, which use the name ``this`` for the new hypothesis.

The notation ``‹p›`` is notation for ``(by assumption : p)``, and can
therefore be used to apply hypotheses in the local context.

As noted in [Constructors, Projections and Matching](#constructors_projections_and_matching),
anonymous constructors and projections and match syntax can be used in proofs just as in expressions that denote data.

.. code-block:: lean

    example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
    assume h₁ : p,
    assume h₂ : q ∧ r,
    have h₃ : q, from and.left h₂,
    show p ∧ q, from and.intro h₁ h₃

    example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
    assume : p,
    assume : q ∧ r,
    have q, from and.left this,
    show p ∧ q, from and.intro ‹p› this

    example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
    assume h₁ : p,
    assume h₂ : q ∧ r,
    suffices h₃ : q, from and.intro h₁ h₃,
    show q, from and.left h₂

Lean also supports a calculational environment, which is introduced with the keyword ``calc``. The syntax is as follows:

.. code-block:: text

    calc
      <expr>_0  'op_1'  <expr>_1  ':'  <proof>_1
        '...'   'op_2'  <expr>_2  ':'  <proof>_2
         ...
        '...'   'op_n'  <expr>_n  ':'  <proof>_n

Each ``<proof>_i`` is a proof for ``<expr>_{i-1} op_i <expr>_i``.

Here is an example:

.. code-block:: lean

    variable (a b c d e : Nat)
    variable h1 : a = b
    variable h2 : b = c + 1
    variable h3 : c = d
    variable h4 : e = 1 + d

    theorem T : a = e :=
    calc
      a     = b      : h1
        ... = c + 1  : h2
        ... = d + 1  : congr_arg _ h3
        ... = 1 + d  : add_comm d (1 : Nat)
        ... =  e     : eq.symm h4

The style of writing proofs is most effective when it is used in conjunction with the ``simp`` and ``rewrite`` tactics.

.. _computation:

Computation
===========

Two expressions that differ up to a renaming of their bound variables are said to be *α-equivalent*, and are treated as syntactically equivalent by Lean.

Every expression in Lean has a natural computational interpretation, unless it involves classical elements that block computation, as described in the next section. The system recognizes the following notions of *reduction*:

* *β-reduction* : An expression ``(λ x, t) s`` β-reduces to ``t[s/x]``, that is, the result of replacing ``x`` by ``s`` in ``t``.
* *ζ-reduction* : An expression ``let x := s in t`` ζ-reduces to ``t[s/x]``.
* *δ-reduction* : If ``c`` is a defined constant with definition ``t``, then ``c`` δ-reduces to ``t``.
* *ι-reduction* : When a function defined by recursion on an inductive type is applied to an element given by an explicit constructor, the result ι-reduces to the specified function value, as described in [Inductive Types](inductive.md).

The reduction relation is transitive, which is to say, is ``s`` reduces to ``s'`` and ``t`` reduces to ``t'``, then ``s t`` reduces to ``s' t'``, ``λ x, s`` reduces to ``λ x, s'``, and so on. If ``s`` and ``t`` reduce to a common term, they are said to be *definitionally equal*. Definitional equality is defined to be the smallest equivalence relation that satisfies all these properties and also includes α-equivalence and the following two relations:

* *η-equivalence* : An expression ``(λx, t x)`` is η-equivalent to ``t``, assuming ``x`` does not occur in ``t``.
* *proof irrelevance* : If ``p : Prop``, ``s : p``, and ``t : p``, then ``s`` and ``t`` are  considered to be equivalent.

This last fact reflects the intuition that once we have proved a proposition ``p``, we only care that is has been proved; the proof does nothing more than witness the fact that ``p`` is true.

Definitional equality is a strong notion of equality of values. Lean's logical foundations sanction treating definitionally equal terms as being the same when checking that a term is well-typed and/or that it has a given type.

The reduction relation is believed to be strongly normalizing, which is to say, every sequence of reductions applied to a term will eventually terminate. The property guarantees that Lean's type-checking algorithm terminates, at least in principle. The consistency of Lean and its soundness with respect to set-theoretic semantics do not depend on either of these properties.

Lean provides two commands to compute with expressions:

* ``#reduce t`` : use the kernel type-checking procedures to carry out reductions on ``t`` until no more reductions are possible, and show the result
* ``#eval t`` : evaluate ``t`` using a fast bytecode evaluator, and show the result

Every computable definition in Lean is compiled to bytecode at definition time. Bytecode evaluation is more liberal than kernel evaluation: types and all propositional information are erased, and functions are evaluated using a stack-based virtual machine. As a result, ``#eval`` is more efficient than ``#reduce,`` and can be used to execute complex programs. In contrast, ``#reduce`` is designed to be small and reliable, and to produce type-correct terms at each step. Bytecode is never used in type checking, so as far as soundness and consistency are concerned, only kernel reduction is part of the trusted computing base.

.. code-block:: lean

    #reduce (fun x => x + 3) 5
    #eval   (fun x => x + 3) 5

    #reduce let x := 5; x + 3
    #eval   let x := 5; x + 3

    def f x := x + 3

    #reduce f 5
    #eval   f 5

    #reduce @Nat.rec (λ n => Nat) (0 : Nat)
                     (λ n recval : Nat => recval + n + 1) (5 : Nat)

    def g : Nat → Nat
    | 0     => 0
    | (n+1) => g n + n + 1

    #reduce g 5
    #eval   g 5

    #eval   g 5000

    example : (fun x => x + 3) 5 = 8 := rfl
    example : (fun x => f x) = f := rfl
    example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

Note: the combination of proof irrelevance and singleton ``Prop`` elimination in ι-reduction renders the ideal version of definitional equality, as described above, undecidable. Lean's procedure for checking definitional equality is only an approximation to the ideal. It is not transitive, as illustrated by the example below. Once again, this does not compromise the consistency or soundness of Lean; it only means that Lean is more conservative in the terms it recognizes as well typed, and this does not cause problems in practice. Singleton elimination will be discussed in greater detail in [Inductive Types](inductive.md).

.. code-block:: lean

    def R (x y : unit) := false
    def accrec := @acc.rec unit R (λ_, unit) (λ _ a ih, ()) ()
    example (h) : accrec h = accrec (acc.intro _ (λ y, acc.inv h)) :=
                  rfl
    example (h) : accrec (acc.intro _ (λ y, acc.inv h)) = () := rfl
    example (h) : accrec h = () := sorry   -- rfl fails


Axioms
======

Lean's foundational framework consists of:

- type universes and dependent function types, as described above

- inductive definitions, as described in [Inductive Types](inductive.md) and
[Inductive Families](declarations.md#inductive-families).

In addition, the core library defines (and trusts) the following axiomatic extensions:

- propositional extensionality:

  .. code-block:: lean

     namespace hide

     -- BEGIN
     axiom propext {a b : Prop} : (a ↔ b) → a = b
     -- END

     end hide

- quotients:

  .. code-block:: lean

     namespace hide
     -- BEGIN
     universes u v

     constant quot      : Π {α : Sort u}, (α → α → Prop) → Sort u

     constant quot.mk   : Π {α : Sort u} (r : α → α → Prop),
                          α → quot r

     axiom    quot.ind  : ∀ {α : Sort u} {r : α → α → Prop}
                            {β : quot r → Prop},
                          (∀ a, β (quot.mk r a)) →
                            ∀ (q : quot r), β q

     constant quot.lift : Π {α : Sort u} {r : α → α → Prop}
                            {β : Sort u} (f : α → β),
                          (∀ a b, r a b → f a = f b) → quot r → β

     axiom quot.sound   : ∀ {α : Type u} {r : α → α → Prop}
                            {a b : α},
                          r a b → quot.mk r a = quot.mk r b
     -- END
     end hide

  ``quot r`` represents the quotient of ``α`` by the smallest equivalence relation containing ``r``. ``quot.mk`` and ``quot.lift`` satisfy the following computation rule:

  .. code-block:: text

     quot.lift f h (quot.mk r a) = f a

- choice:

  .. code-block:: lean

     namespace hide
     universe u

     -- BEGIN
     axiom choice {α : Sort u} : nonempty α → α
     -- END

     end hide

  Here ``nonempty α`` is defined as follows:

  .. code-block:: lean

     namespace hide
     universe u

     -- BEGIN
     class inductive nonempty (α : Sort u) : Prop
     | intro : α → nonempty
     -- END

     end hide

  It is equivalent to  ``∃ x : α, true``.

The quotient construction implies function extensionality. The ``choice`` principle, in conjunction with the others, makes the axiomatic foundation classical; in particular, it implies the law of the excluded middle and propositional decidability. Functions that make use of ``choice`` to produce data are incompatible with a computational interpretation, and do not produce bytecode. They have to be declared ``noncomputable``.

For metaprogramming purposes, Lean also allows the definition of objects which stand outside the object language. These are denoted with the ``meta`` keyword, as described in [Metaprogramming](metaprogramming.md).
