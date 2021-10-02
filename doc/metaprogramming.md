# Metaprogramming

Macros are a language feature that allows writing code that writes other code (metaprogramming).

In Lean 4, macros are used pervasively. So much so that core language features such as `do` notation
is implemented via macros! As a language user, macros are useful to easily
embed domain-specific languages and to generate code at compile-time, to name a few uses.


#### Balanced Parentheses as an Embedded Domain Specific Language

Let's look at how to use macros to extend the Lean 4 parser and embed a language for building _balanced parentheses_.
This language accepts strings given by the [BNF grammar](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form)

```
Dyck := 
  "(" Dyck ")" 
  | "{" Dyck '}'
  | "End"
```

We begin by defining an inductive data type of the grammar we wish to parse:

```lean
inductive Dyck: Type :=
   | Round : Dyck -> Dyck -- ( <inner> )
   | Flower : Dyck -> Dyck -- { <inner> }
   | End : Dyck
```

We begin by declaring a _syntax category_ using the `declare_syntax_cat <category>` command.
This names our grammar and allows us to specify parsing rules associated with our grammar.

```lean
declare_syntax_cat brack
```

Next, we specify the grammar using the `syntax <parse rule>` directive:

```lean
syntax "End" : brack
```

The above means that the string "End" lives in syntax category `brack`.

Similarly, we declare the rules `"(" Dyck ")"` and `"{" Dyck "}"` using the rules:

```lean
syntax "(" brack ")" : brack
syntax "{" brack "}" : brack
```

Finally, we need a way to build _Lean 4 terms_ from this grammar -- that is, we must translate out of this
grammar into a `Dyck` value, which is a Lean 4 term. For this, we create a piece of syntax,
called `fromBrack% brack : term`, which receives a `brack` and produces a `term`.

```lean
-- auxiliary notation for translating `brack` into `term`
syntax "fromBrack% " brack : term
```

To specify the transformation rules, we use `macro_rules` to declare how the syntax `fromBrack% <brack>`
produces terms. This is written using a pattern-matching style syntax, where the left-hand side
declares the pattern to be matched, and the right-hand side declares the production. Syntax placeholders (antiquotations)
are introduced via the `$<var-name>` syntax. The right-hand side is
an arbitrary Lean term that we are producing.

```lean
macro_rules
  | `(fromBrack% End) => `(Dyck.End)
  | `(fromBrack% ( $b )) => `(Dyck.Round (fromBrack% $b)) -- recurse
  | `(fromBrack% { $b }) => `(Dyck.Flower (fromBrack% $b)) -- recurse
```


```lean
def bar : Dyck := fromBrack% End
#print bar
/-
def bar : Dyck :=
Dyck.End
-/

def foo : Dyck := fromBrack% {(End)}
#print foo
/-
Dyck.Flower (Dyck.Round (Dyck.End))
-/
```


In summary, we've seen:
- How to declare a syntax category for the Dyck grammar.
- How to specify parse trees of this grammar using `syntax`
- How to translate out of this grammar into Lean 4 terms using `macro_rules`.

The full program listing is given below:


```lean
inductive Dyck: Type :=
   | Round : Dyck -> Dyck -- ( <inner> )
   | Flower : Dyck -> Dyck -- { <inner> }
   | End : Dyck


-- | declare Dyck grammar parse trees
declare_syntax_cat brack
syntax "End" : brack
syntax "(" brack ")" : brack
syntax "{" brack "}" : brack


-- auxiliary notation for translating `brack` into `term`
syntax "fromBrack% " brack : term

-- | rules to translate dyck grammar into inductive value of type Dyck.
macro_rules
  | `(fromBrack% End) => `(Dyck.End)
  | `(fromBrack% ( $b )) => `(Dyck.Round (fromBrack% $b)) -- recurse
  | `(fromBrack% { $b }) => `(Dyck.Flower (fromBrack% $b)) -- recurse

-- | tests
def bar : Dyck := fromBrack% End
#print bar
/-
def bar : Dyck :=
Dyck.End
-/

def foo : Dyck := fromBrack% {(End)}
#print foo
/-
Dyck.Flower (Dyck.Round Dyck.End)
-/
```

## References
- [Hygenic Macro Expansion for Theorem Proving Languages](https://arxiv.org/abs/2001.10490)
