# Significant changes from Lean 3

Lean 4 is not backward compatible with Lean 3.
We have rewritten most of the system, and took the opportunity to cleanup the syntax,
metaprogramming framework, and elaborator. In this section, we go over the most significant
changes.

## Lambda expressions

We do not use `,` anymore to separate the binders from the lambda expression body.
The Lean 3 syntax for lambda expressions was unconventional, and `,` has been overused in Lean 3.
For example, we believe a list of lambda expressions is quite confusing in Lean 3, since `,` is used
to separate the elements of a list, and in the lambda expression itself. We now use `=>` as the separator,
as an example, `fun x => x` is the identity function. One may still use the symbol `λ` as a shorthand for `fun`.
The lambda expression notation has many new features that are not supported in Lean 3.

## Pattern matching

In Lean 4, one can easily create new notation that abbreviates commonly used idioms. One of them is a
`fun` followed by a `match`. In the following examples, we define a few functions using `fun`+`match` notation.

```lean
# namespace ex1
def Prod.str : Nat × Nat → String :=
  fun (a, b) => "(" ++ toString a ++ ", " ++ toString b ++ ")"

structure Point where
  x : Nat
  y : Nat
  z : Nat

def Point.addX : Point → Point → Nat :=
  fun { x := a, .. } { x := b, .. } =>  a+b

def Sum.str : Option Nat → String :=
  fun
    | some a => "some " ++ toString a
    | none   => "none"
# end ex1
```

## Implicit lambdas

In Lean 3 stdlib, we find many [instances](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39) of the dreadful `@`+`_` idiom.
It is often used when the expected type is a function type with implicit arguments,
and we have a constant (`reader_t.pure` in the example) which also takes implicit arguments. In Lean 4, the elaborator automatically introduces lambdas
for consuming implicit arguments. We are still exploring this feature and analyzing its impact, but the experience so far has been very positive. As an example,
here is the example in the link above using Lean 4 implicit lambdas.

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

Users can disable the implicit lambda feature by using `@` or writing a lambda expression with `{}` or `[]` binder annotations.
Here are few examples

```lean
# namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
# end ex2
```

## Sugar for simple functions

In Lean 3, we can create simple functions from infix operators by using parentheses. For example, `(+1)` is sugar for `fun x, x + 1`. In Lean 4, we generalize this notation using `·` As a placeholder. Here are a few examples:

```lean
# namespace ex3
#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
# end ex3
```

As in Lean 3, the notation is activated using parentheses, and the lambda abstraction is created by collecting the nested `·`s.
The collection is interrupted by nested parentheses. In the following example, two different lambda expressions are created.

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

## Function applications

In Lean 4, we have support for named arguments.
Named arguments enable you to specify an argument for a parameter by matching the argument with
its name rather than with its position in the parameter list.
If you don't remember the order of the parameters but know their names,
you can send the arguments in any order. You may also provide the value for an implicit parameter when
Lean failed to infer it. Named arguments also improve the readability of your code by identifying what
each argument represents.

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```
In the following examples, we illustrate the interaction between named and default arguments.

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

In Lean 4, we can use `..` to provide missing explicit arguments as `_`.
This feature combined with named arguments is useful for writing patterns. Here is an example:
```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | add    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```
Ellipsis are also useful when explicit argument can be automatically inferred by Lean, and we want
to avoid a sequence of `_`s.
```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```

## Dependent function types

Given `α : Type` and `β : α → Type`, `(x : α) → β x` denotes the type of functions `f` with the property that,
for each `a : α`, `f a` is an element of `β a`. In other words, the type of the value returned by `f` depends on its input.
We say `(x : α) → β x` is a dependent function type. In Lean 3, we write the dependent function type `(x : α) → β x` using
one of the following three equivalent notations:
`forall x : α, β x` or `∀ x : α, β x` or `Π x : α, β x`.
The first two were intended to be used for writing propositions, and the latter for writing code.
Although the notation `Π x : α, β x` has historical significance, we have removed it from Lean 4 because
it is awkward to use and often confuses new users. We can still write `forall x : α, β x` and `∀ x : α, β x`.

```lean
#check forall (α : Type), α → α
#check ∀ (α : Type), α → α
#check ∀ α : Type, α → α
#check ∀ α, α → α
#check (α : Type) → α → α
#check {α : Type} → (a : Array α) → (i : Nat) → i < a.size → α
#check {α : Type} → [ToString α] → α → String
#check forall {α : Type} (a : Array α) (i : Nat), i < a.size → α
#check {α β : Type} → α → β → α × β
```

## The `meta` keyword

In Lean 3, the keyword `meta` is used to mark definitions that can use primitives implemented in C/C++.
These metadefinitions can also call themselves recursively, relaxing the termination
restriction imposed by ordinary type theory. Metadefinitions may also use unsafe primitives such as
`eval_expr (α : Type u) [reflected α] : expr → tactic α`, or primitives that break referential transparency
`tactic.unsafe_run_io`.

The keyword `meta` has been currently removed from Lean 4. However, we may re-introduce it in the future,
but with a much more limited purpose: marking meta code that should not be included in the executables produced by Lean.

The keyword `constant` has been deleted in Lean 4, and `axiom` should be used instead. In Lean 4, the new command `opaque` is used to define an opaque definition. Here are two simple examples:
```lean
# namespace meta1
opaque x : Nat := 1
-- The following example will not type check since `x` is opaque
-- example : x = 1 := rfl

-- We can evaluate `x`
#eval x
-- 1

-- When no value is provided, the elaborator tries to build one automatically for us
-- using the `Inhabited` type class
opaque y : Nat
# end meta1
```

We can instruct Lean to use a foreign function as the implementation for any definition
using the attribute `@[extern "foreign_function"]`. It is the user's responsibility to ensure the
foreign implementation is correct.
However, a user mistake here will only impact the code generated by Lean, and
it will **not** compromise the logical soundness of the system.
That is, you cannot prove `False` using the `@[extern]` attribute.
We use `@[extern]` with definitions when we want to provide a reference implementation in Lean
that can be used for reasoning. When we write a definition such as
```lean
@[extern "lean_nat_add"]
def add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (add a b)
```
Lean assumes that the foreign function `lean_nat_add` implements the reference implementation above.

The `unsafe` keyword allows us to define functions using unsafe features such as general recursion,
and arbitrary type casting. Regular (safe) functions cannot directly use `unsafe` ones since it would
compromise the logical soundness of the system. As in regular programming languages, programs written
using unsafe features may crash at runtime. Here are a few unsafe examples:
```lean
unsafe def unsound : False :=
  unsound

#check @unsafeCast
-- {α : Type _} → {β : Type _} → α → β

unsafe def nat2String (x : Nat) : String :=
  unsafeCast x

-- The following definition doesn't type check because it is not marked as `unsafe`
-- def nat2StringSafe (x : Nat) : String :=
--   unsafeCast x
```

The `unsafe` keyword is particularly useful when we want to take advantage of an implementation detail of the
Lean execution runtime. For example, we cannot prove in Lean that arrays have a maximum size, but
the runtime used to execute Lean programs guarantees that an array cannot have more than 2^64 (2^32) elements
in a 64-bit (32-bit) machine. We can take advantage of this fact to provide a more efficient implementation for
array functions. However, the efficient version would not be very useful if it can only be used in
unsafe code. Thus, Lean 4 provides the attribute `@[implemented_by functionName]`. The idea is to provide
an unsafe (and potentially more efficient) version of a safe definition or constant. The function `f`
at the attribute `@[implemented_by f]` is very similar to an extern/foreign function,
the key difference is that it is implemented in Lean itself. Again, the logical soundness of the system
cannot be compromised by using the attribute `implemented_by`, but if the implementation is incorrect your
program may crash at runtime. In the following example, we define `withPtrUnsafe a k h` which
executes `k` using the memory address where `a` is stored in memory. The argument `h` is proof
that `k` is a constant function. Then, we "seal" this unsafe implementation at `withPtr`. The proof `h`
ensures the reference implementation `k 0` is correct. For more information, see the article
"Sealing Pointer-Based Optimizations Behind Pure Functions".
```lean
unsafe
def withPtrUnsafe {α β : Type} (a : α) (k : USize → β) (h : ∀ u, k u = k 0) : β :=
  k (ptrAddrUnsafe a)

@[implemented_by withPtrUnsafe]
def withPtr {α β : Type} (a : α) (k : USize → β) (h : ∀ u, k u = k 0) : β :=
  k 0
```

General recursion is very useful in practice, and it would be impossible to implement Lean 4 without it.
The keyword `partial` implements a very simple and efficient approach for supporting general recursion.
Simplicity was key here because of the bootstrapping problem. That is, we had to implement Lean in Lean before
many of its features were implemented (e.g., the tactic framework or support for wellfounded recursion).
Another requirement for us was performance. Functions tagged with `partial` should be as efficient as the ones implemented in mainstream functional programming
languages such as OCaml. When the `partial` keyword is used, Lean generates an auxiliary `unsafe` definition that
uses general recursion, and then defines an opaque constant that is implemented by this auxiliary definition.
This is very simple, efficient, and is sufficient for users that want to use Lean as a regular programming language.
A `partial` definition cannot use unsafe features such as `unsafeCast` and `ptrAddrUnsafe`, and it can only be used to
implement types we already known to be inhabited. Finally, since we "seal" the auxiliary definition using an opaque
constant, we cannot reason about `partial` definitions.

We are aware that proof assistants such as Isabelle provide a framework for defining partial functions that does not
prevent users from proving properties about them. This kind of framework can be implemented in Lean 4. Actually,
it can be implemented by users since Lean 4 is an extensible system. The developers current have no plans to implement
this kind of support for Lean 4. However, we remark that users can implement it using a function that traverses
the auxiliary unsafe definition generated by Lean, and produces a safe one using an approach similar to the one used in Isabelle.

```lean
# namespace partial1
partial def f (x : Nat) : IO Unit := do
  IO.println x
  if x < 100 then
     f (x+1)

#eval f 98
# end partial1
```

## Library changes

These are changes to the library which may trip up Lean 3 users:

- `List` is no longer a monad.

## Style changes

Coding style changes have also been made:

- Term constants and variables are now `lowerCamelCase` rather than `snake_case`
- Type constants are now `UpperCamelCase`, eg `Nat`, `List`. Type variables are still lower case greek letters. Functors are still lower case latin `(m : Type → Type) [Monad m]`.
- When defining typeclasses, prefer not to use "has". Eg `ToString` or `Add` instead of `HasToString` or `HasAdd`.
- Prefer `return` to `pure` in monad expressions.
- Pipes `<|` are preferred to dollars `$` for function application.
- Declaration bodies should always be indented:
  ```lean
  inductive Hello where
    | foo
    | bar

  structure Point where
    x : Nat
    y : Nat

  def Point.addX : Point → Point → Nat :=
    fun { x := a, .. } { x := b, .. } => a + b
  ```
- In structures and typeclass definitions, prefer `where` to `:=` and don't surround fields with parentheses. (Shown in `Point` above)
