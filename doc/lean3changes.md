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

* Pattern matching

In Lean 4, one can easily create new notation that abbreviates commonly used idioms. One of the them is a
`fun` followed by a `match`. In the following examples, we define a few functions using `fun`+`match` notation.

```lean
def Prod.str : Nat × Nat → String :=
  fun (a, b) => "(" ++ toString a ++ ", " ++ toString b ++ ")"

structure Point :=
  (x y z : Nat)

def Point.addX : Point → Point → Nat :=
  fun { x := a, .. } { x := b, .. } =>  a+b

def Sum.str : Option Nat → String :=
  fun
    | some a => "some " ++ toString a
    | none   => "none"
```

* Implicit lambdas

In Lean 3 stdlib, we find many [instances](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39) of dreaful `@`+`_` idiom.
It is often used when we the expected type is a function type with implicit arguments,
and we have a constant (`reader_t.pure` in the example) which also takes implicit arguments. In Lean 4, the elaborator automatically introduces lambda's
for consuming implicit arguments. We are still exploring this feature and analyzing its impact, but the experience so far has been very positive. As an example,
here is the example in the link above using Lean 4 implicit lambdas.

```lean
instance : Monad (ReaderT ρ m) := {
  pure := ReaderT.pure,
  bind := ReaderT.bind
}
```

Users can disable the implicit lambda feature by using `@` or writing a lambda expression with `{}` or `[]` binder annotations.
Here are few examples

```lean
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because we use `@` before `fun`
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
```

* Sugar for simple functions

In Lean 3, we can creating simple functions from infix operators by using parentheses. For example, `(+1)` is sugar for `fun x, x + 1`. In Lean 4, we generalize this notation using `·` as a placeholder. Here are a few examples:

```lean
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

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a) : p a a b :=
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

variables {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

In Lean 4, we can use `..` to provide missing explicit arguments as `_`.
This feature combined with named arguments is useful for writing patterns. Here is an example:
```lean
inductive Term
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
  congrArg f (Nat.addAssoc ..)
```
