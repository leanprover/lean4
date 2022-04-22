# Balanced Parentheses as an Embedded Domain Specific Language

Let's look at how to use macros to extend the Lean 4 parser and embed a language for building _balanced parentheses_.
This language accepts strings given by the [BNF grammar](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form)

```
Dyck ::=
  "(" Dyck ")"
  | "{" Dyck "}"
  | end
```

We begin by defining an inductive data type of the grammar we wish to parse:

```lean,ignore
inductive Dyck : Type where
  | round : Dyck → Dyck  -- ( <inner> )
  | curly : Dyck → Dyck  -- { <inner> }
  | leaf : Dyck
```

We begin by declaring a _syntax category_ using the `declare_syntax_cat <category>` command.
This names our grammar and allows us to specify parsing rules associated with our grammar.

```lean,ignore
declare_syntax_cat brack
```

Next, we specify the grammar using the `syntax <parse rule>` command:

```lean,ignore
syntax "end" : brack
```

The above means that the token "end" lives in syntax category `brack`.

Similarly, we declare the rules `"(" Dyck ")"` and `"{" Dyck "}"` using the rules:

```lean,ignore
syntax "(" brack ")" : brack
syntax "{" brack "}" : brack
```

Finally, we need a way to build _Lean 4 terms_ from this grammar -- that is, we must translate out of this
grammar into a `Dyck` value, which is a Lean 4 term. For this, we create a new kind of "quotation" that
consumes syntax in `brack` and produces a `term`.

```lean,ignore
syntax "`[Dyck| " brack "]" : term
```

To specify the transformation rules, we use `macro_rules` to declare how the syntax `` `[Dyck| <brack>] ``
produces terms. This is written using a pattern-matching style syntax, where the left-hand side
declares the syntax pattern to be matched, and the right-hand side declares the production. Syntax placeholders (antiquotations)
are introduced via the `$<var-name>` syntax. The right-hand side is
an arbitrary Lean term that we are producing.

```lean,ignore
macro_rules
  | `(`[Dyck| end])    => `(Dyck.leaf)
  | `(`[Dyck| ($b)]) => `(Dyck.round `[Dyck| $b])  -- recurse
  | `(`[Dyck| {$b}]) => `(Dyck.curly `[Dyck| $b])  -- recurse
```


```lean,ignore
#check `[Dyck| end]      -- Dyck.leaf
#check `[Dyck| {(end)}]  -- Dyck.curl (Dyck.round Dyck.leaf)
```

In summary, we've seen:
- How to declare a syntax category for the Dyck grammar.
- How to specify parse trees of this grammar using `syntax`
- How to translate out of this grammar into Lean 4 terms using `macro_rules`.

The full program listing is given below:

```lean
{{#include syntax_example.lean}}
```
