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
inductive Arith: Type where
 | add : Arith -> Arith -> Arith -- e + f
 | mul : Arith -> Arith -> Arith -- e * f
 | int : Int -> Arith -- constant
 | symbol : String -> Arith -- variable
```

We declare a syntax category to describe the grammar that we will be parsing.
See that we control the precedence of `:+` and `:*` by writing `syntax:50` for addition and `syntax:60` for multiplication,
indicating that multiplication binds tighter than addition (higher the number, tighter the binding).
This allows us to declare _precedence_ when defining new syntax.

```lean,ignore
declare_syntax_cat arith
syntax term : arith -- int for Arith.int
syntax str : arith -- strings for Arith.Symbol
syntax:50  arith "+" arith : arith -- Arith.add
syntax:60 arith "*" arith : arith -- Arith.mul
syntax "(" arith ")" : arith -- bracketed expressions
```

We define the macro `Arith|` to translate the syntax category `arith` into an `Arith` inductive value that lives in `term`:


```
-- auxiliary notation for translating `arith` into `term`
syntax "Arith| " arith : term
```

Our macro rules perform the "obvious" translation:

```lean,ignore
macro_rules
  | `(Arith| $s:strLit) => `(Arith.Symbol $s)
  | `(Arith| $num:term) => `(Arith.Symbol $num)
  | `(Arith| $x:arith :+ $y:arith ) => `(Arith.add (Arith| $x) (Arith| $y))
  | `(Arith| $x:arith :* $y:arith ) => `(Arith.mul (Arith| $x) (Arith| $y))
  | `(Arith| ($x:arith)) => `(Arith| $x)
```
And some examples:

```lean,ignore
def foo := (Arith| "x" * "y") -- mul
#print foo
/-
def foo : Arith :=
Arith.mul (Arith.symbol "x") (Arith.symbol "y")
-/

def bar := (Arith| "x" + "y") -- add
#print bar
/-
def bar : Arith :=
Arith.add (Arith.symbol "x") (Arith.symbol "y")
-/

def baz := (Arith| "x" + 20) -- symbol + int
#print baz
/-
def baz : Arith :=
Arith.add (Arith.symbol "x") (Arith.int 20)
-/
```

All the basic examples work. Let's check that we get precedence right as well:


```
def quux := (Arith| "x" + "y" * "z") -- precedence
#print quux
/-
def quux : Arith :=
Arith.add (Arith.symbol "x") (Arith.mul (Arith.symbol "y") (Arith.symbol "z"))
-/

def quuz := (Arith| ("x" + "y") * "z") -- brackets
#print quuz
/-
def quuz : Arith :=
Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")
-/
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
  | `(Arith| $x:ident) => `(Arith.Symbol $(Lean.quote (toString x.getId)))
```


Let's test and see that we can now write expressions such as `x :* y` directly instead of having to write `"x" :* "y"`:

```lean,ignore
def x_ident := Arith| x 
#print x_ident
/-
def x_ident : Arith :=
Arith.symbol "x"
-/

def x_plus_y : Arith := (Arith| x + y)
#print x_plus_y
/-
def x_plus_y : Arith :=
Arith.add (Arith.symbol "x") (Arith.symbol "y")
-/
```

We now show an unfortunate consequence of the above definitions. Suppose we want to build `(x :+ y) :+ z)`.
Since we already have defined `x_plus_y` as `x := y`, perhaps we should reuse it! Let's try:

```lean,ignore
def x_plus_y_plus_z := (Arith| x_plus_y + z)
#print x_plus_y_plus_z
/-
def x_plus_y_plus_z : Arith :=
Arith.add (Arith.symbol "x_plus_y") (Arith.symbol "z")
-/
```

Whoops, that didn't work! What happened? Lean treats `x_plus_y` _itself_ as an identifier! So we need to add some syntax
to be able to "escape" the `Arith|` context. Let's use the syntax `<[ $e:term ]>` to mean: evaluate `$e` as a real term,
not an identifier. The macro looks like follows:

```lean,ignore
syntax "<[" term "]>" : arith -- escape for embedding terms into `Arith`
macro_rules
  | `(Arith| <[ $e:term ]>) => e

```

Let's try our previous example:

```lean,ignore
def x_plus_y_plus_z2 := Arith| <[ x_plus_y ]>
#print x_plus_y_plus_z2
/-
def x_plus_y_plus_z2 : Arith :=
x_plus_y
-/
```

Perfect!

In this tutorial, we expanded on the previous tutorial to parse a more
realistic grammar with multiple levels of precedence, how to parse identifiers directly
within a macro, and how to provide an escape from within the macro context.

#### Full code listing

```lean
-- example on parsing arith language via macros
inductive Arith: Type where
  | add : Arith -> Arith -> Arith -- e + f
  | mul : Arith -> Arith -> Arith -- e * f
  | int : Int -> Arith -- constant
  | symbol : String -> Arith -- variable

declare_syntax_cat arith

syntax num : arith -- int for Arith.int
syntax str : arith -- strings for Arith.symbol
syntax:60  arith "+" arith : arith -- Arith.add
syntax:70 arith "*" arith : arith -- Arith.mul
syntax "(" arith ")" : arith -- bracketed expressions

-- auxiliary notation for translating `arith` into `term`
syntax "Arith| " arith : term

macro_rules
  | `(Arith| $s:strLit) => `(Arith.symbol $s)
  | `(Arith| $num:numLit) => `(Arith.int $num)
  | `(Arith| $x:arith + $y:arith) => `(Arith.add (Arith| $x) (Arith| $y))
  | `(Arith| $x:arith * $y:arith) => `(Arith.mul (Arith| $x) (Arith| $y))
  | `(Arith| ($x:arith)) => `(Arith| $x)

def foo := (Arith| "x" * "y") -- mul
#print foo
/-
def foo : Arith :=
Arith.mul (Arith.symbol "x") (Arith.symbol "y")
-/

def bar := (Arith| "x" + "y") -- add
#print bar
/-
def bar : Arith :=
Arith.add (Arith.symbol "x") (Arith.symbol "y")
-/

def baz := (Arith| "x" + 20) -- symbol + int
#print baz
/-
def baz : Arith :=
Arith.add (Arith.symbol "x") (Arith.int 20)
-/


def quux := (Arith| "x" + "y" * "z") -- precedence
#print quux
/-
def quux : Arith :=
Arith.add (Arith.symbol "x") (Arith.mul (Arith.symbol "y") (Arith.symbol "z"))
-/

def quuz := (Arith| ("x" + "y") * "z") -- brackets
#print quuz
/-
def quuz : Arith :=
Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")
-/

syntax ident : arith

macro_rules
  | `(Arith| $x:ident) => `(Arith.symbol $(Lean.quote (toString x.getId)))

def x_ident := Arith| x 
#print x_ident
/-
def x_ident : Arith :=
Arith.symbol "x"
-/

def x_plus_y : Arith := (Arith| x + y)
#print x_plus_y
/-
def x_plus_y : Arith :=
Arith.add (Arith.symbol "x") (Arith.symbol "y")
-/

def x_plus_y_plus_z := (Arith| x_plus_y + z)
#print x_plus_y_plus_z
/-
def x_plus_y_plus_z : Arith :=
Arith.add (Arith.symbol "x_plus_y") (Arith.symbol "z")
-/

syntax "<[" term "]>" : arith -- escape for embedding terms into `Arith`
 
macro_rules
  | `(Arith| <[ $e:term ]>) => e
  

def x_plus_y_plus_z2 := (Arith| <[ x_plus_y ]>)
#print x_plus_y_plus_z2
/-
def x_plus_y_plus_z2 : Arith :=
x_plus_y
-/
```

