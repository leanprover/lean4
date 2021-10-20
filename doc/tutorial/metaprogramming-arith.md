## Arithmetic as an embedded domain-specific language

Let's parse another classic grammar, the grammar of arithmetic expressions with
addition, multiplication, integers, and variables.  In the process, we'll learn
how to:

- Convert identifiers such as `x` into strings within a macro.
- add the ability to "escape" the macro context from within the macro. This is useful to interpret identifiers with their _original_ meaning (predefined values)
  instead of their new meaning within a macro (treat as a symbol).

Let's begin with the simplest thing possible. We'll define an AST, and use operators `+` and `*` to denote
building an arithmetic AST.


Here's the AST that we will be parsing:

```lean,ignore
-- example on parsing arith language via macros
inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | int : Int → Arith -- constant
  | symbol : String → Arith -- variable
```

We declare a syntax category to describe the grammar that we will be parsing.
See that we control the precedence of `+` and `*` by writing `syntax:50` for addition and `syntax:60` for multiplication,
indicating that multiplication binds tighter than addition (higher the number, tighter the binding).
This allows us to declare _precedence_ when defining new syntax.

```lean,ignore
declare_syntax_cat arith
syntax num : arith -- int for Arith.int
syntax str : arith -- strings for Arith.symbol
syntax:60  arith:60 "+" arith:61 : arith -- Arith.add
syntax:70 arith:70 "*" arith:71 : arith -- Arith.mul
syntax "(" arith ")" : arith -- bracketed expressions
```

Further, if we look at `syntax:60  arith:60 "+" arith:61 : arith`, the
precedence declarations at `arith:60 "+" arith:61` conveys that the left
argument must have precedence at least `60` or greater, and the right argument
must have precedence at least`61` or greater.  Note that this forces left
associativity. To understand this, let's compare two hypothetical parses:

```
-- syntax:60  arith:60 "+" arith:61 : arith -- Arith.add
-- a + b + c
(a:60 + b:61):60 + c
a + (b:60 + c:61):60
```

In the parse tree of `a + (b:60 + c:61):60`, we see that the right argument `(b + c)` is given the precedence `60`. However,
the rule for addition expects the right argument to have a precedence of **at least** 61, as witnessed by the `arith:61` at
the right-hand-side of `syntax:60 arith:60 "+" arith:61 : arith`. Thus, the rule `syntax:60  arith:60 "+" arith:61 : arith`
ensures that addition is left associative.

Since addition is declared arguments of precedence `60/61` and multiplication with `70/71`, this causes multiplication to bind
tighter than addition. Once again, let's compare two hypothetical parses:

```
-- syntax:60  arith:60 "+" arith:61 : arith -- Arith.add
-- syntax:70 arith:70 "*" arith:71 : arith -- Arith.mul
-- a * b + c
a * (b:60 + c:61):60
(a:70 * b:71):70 + c
```

While parsing `a * (b + c)`, `(b + c)` is assigned a precedence `60` by the addition rule. However, multiplication expects
the right argument to have precedence **at least** 71. Thus, this parse is invalid. In contrast, `(a * b) + c` assigns
a precedence of `70` to `(a * b)`. This is compatible with addition which expects the left argument to have precedence
**at least `60` ** (`70` is greater than `60`). Thus, the string `a * b + c` is parsed as `(a * b) + c`.
For more details, please look at the [Lean manual on syntax extensions](../syntax.md#notations-and-precedence).




To go from strings into `Arith`, We define a macro to
translate the syntax category `arith` into an `Arith` inductive value that
lives in `term`:


```lean,ignore
-- auxiliary notation for translating `arith` into `term`
syntax "`[Arith| " arith "]" : term
```

Our macro rules perform the "obvious" translation:

```lean,ignore
macro_rules
  | `(`[Arith| $s:strLit ]) => `(Arith.symbol $s)
  | `(`[Arith| $num:numLit ]) => `(Arith.int $num)
  | `(`[Arith| $x:arith + $y:arith ]) => `(Arith.add `[Arith| $x] `[Arith| $y])
  | `(`[Arith| $x:arith * $y:arith ]) => `(Arith.mul `[Arith| $x] `[Arith| $y])
  | `(`[Arith| ($x:arith) ]) => `(`[Arith| $x ])
```
And some examples:

```lean,ignore
#check `[Arith| "x" * "y"] -- Arith.mul (Arith.symbol "x") (Arith.symbol "y") : Arith

#check `[Arith| "x" + "y"] -- add
-- Arith.add (Arith.symbol "x") (Arith.symbol "y") 

#check  `[Arith| "x" + 20] -- symbol + int
-- Arith.add (Arith.symbol "x") (Arith.int 20)


#check `[Arith| "x" + "y" * "z" ] -- precedence
Arith.add (Arith.symbol "x") (Arith.mul (Arith.symbol "y") (Arith.symbol "z"))
-- 
#check `[Arith| "x" * "y" + "z"] -- precedence
-- Arith.add (Arith.mul (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")


#check `[Arith| ("x" + "y") * "z"] -- brackets
-- Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")
```


Writing variables as strings, such as `"x"`  gets old; Wouldn't it be so much
prettier if we could write `x * y`, and have the macro translate this into `Arith.mul (Arith.Symbol "x") (Arith.mul "y")`?
We can do this, and this will be our first taste of manipulating macro variables --- we'll use `x.getId` instead of directly evaluating `$x`.
We also write a macro rule for `Arith|` that translates an identifier into
a string, using `$(Lean.quote (toString x.getId))`.  (TODO: explain what
`Lean.quote` does):

```lean,ignore
syntax ident : arith

macro_rules
  | `(`[Arith| $x:ident]) => `(Arith.symbol $(Lean.quote (toString x.getId)))
```


Let's test and see that we can now write expressions such as `x * y` directly instead of having to write `"x" * "y"`:

```lean,ignore
#check `[Arith| x ] -- Arith.symbol "x"

#check `[Arith| x + y] -- Arith.add (Arith.symbol "x") (Arith.symbol "y")
```

We now show an unfortunate consequence of the above definitions. Suppose we want to build `(x + y) + z)`.
Since we already have defined `x_plus_y` as `x + y`, perhaps we should reuse it! Let's try:

```lean,ignore
#check `[Arith| x_plus_y + z] --Arith.add (Arith.symbol "x_plus_y") (Arith.symbol "z")
```

Whoops, that didn't work! What happened? Lean treats `x_plus_y` _itself_ as an identifier! So we need to add some syntax
to be able to "escape" the `Arith|` context. Let's use the syntax `<[ $e:term ]>` to mean: evaluate `$e` as a real term,
not an identifier. The macro looks like follows:

```lean,ignore
syntax "<[" term "]>" : arith -- escape for embedding terms into `Arith`
macro_rules
  | `(`[Arith| <[ $e:term ]> ]) => e

```

Let's try our previous example:

```lean,ignore
#check `[Arith| <[ x_plus_y ]>] -- x_plus_y
```

Perfect!

In this tutorial, we expanded on the previous tutorial to parse a more
realistic grammar with multiple levels of precedence, how to parse identifiers directly
within a macro, and how to provide an escape from within the macro context.

#### Full code listing

```lean
-- example on parsing arith language via macros
inductive Arith: Type
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | int : Int → Arith -- constant
  | symbol : String → Arith -- variable

declare_syntax_cat arith

syntax num : arith -- int for Arith.int
syntax str : arith -- strings for Arith.symbol
syntax:60  arith:60 "+" arith:61 : arith -- Arith.add
syntax:70 arith:70 "*" arith:71 : arith -- Arith.mul
syntax "(" arith ")" : arith -- bracketed expressions

-- auxiliary notation for translating `arith` into `term`
syntax "`[Arith| " arith "]" : term

macro_rules
  | `(`[Arith| $s:strLit ]) => `(Arith.symbol $s )
  | `(`[Arith| $num:numLit ]) => `(Arith.int $num )
  | `(`[Arith| $x:arith + $y:arith ]) => `(Arith.add `[Arith| $x] `[Arith| $y] )
  | `(`[Arith| $x:arith * $y:arith ]) => `(Arith.mul `[Arith| $x] `[Arith| $y] )
  | `(`[Arith| ($x:arith) ]) => `(`[Arith| $x ])

def foo := 
#check `[Arith| "x" * "y" ] -- mul
-- Arith.mul (Arith.symbol "x") (Arith.symbol "y")

def bar := 
#check `[Arith| "x" + "y"] -- add
-- Arith.add (Arith.symbol "x") (Arith.symbol "y")

def baz := 
#check `[Arith| "x" + 20] -- symbol + int
-- Arith.add (Arith.symbol "x") (Arith.int 20)

def quux_left := 
#check `[Arith| "x" + "y" * "z" ] -- precedence
-- Arith.add (Arith.symbol "x") (Arith.mul (Arith.symbol "y") (Arith.symbol "z"))

def quux_right := 
#check `[Arith| "x" * "y" + "z"] -- precedence
-- Arith.add (Arith.mul (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")


def quuz := 
#check `[Arith| ("x" + "y") * "z"] -- brackets
-- Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")

syntax ident : arith

macro_rules
  | `(`[Arith| $x:ident]) => `(Arith.symbol $(Lean.quote (toString x.getId)))

#check `[Arith| x ] -- Arith.symbol "x"
#check `[Arith| x + y] -- Arith.add (Arith.symbol "x") (Arith.symbol "y")
#check `[Arith| x_plus_y + z] -- Arith.add (Arith.symbol "x_plus_y") (Arith.symbol "z")

syntax "<[" term "]>" : arith -- escape for embedding terms into `Arith`
 
macro_rules
  | `(`[Arith| <[ $e:term ]> ]) => e
  

#check `[Arith| <[ x_plus_y ]>] -- x_plus_y
```

