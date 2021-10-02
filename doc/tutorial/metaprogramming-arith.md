## Arithmetic as an embedded domain-specific language

Let's parse another classic grammar, the grammar of arithmetic expressions with
addition, multiplication, integers, and variables.  In the process, we'll learn
how to:

- Convert identifiers such as `x` into strings within a macro.
- Add the ability to "escape" the macro context from within the macro. This is useful to interpret identifiers with their _original_ meaning (predefined values)
  instead of their new meaning within a macro (treat as a symbol).

Let's begin with the simplest thing possible. We'll define an AST, and use operators `:+` and `:*` to denote
building an arithmetic AST. We use `:+` and `:*` instead of `+` and `*` to avoid clashing names.


Here's the AST that we will be parsing:

```lean,ignore
-- example on parsing arith language via macros
inductive Arith: Type :=
   | Add : Arith -> Arith -> Arith -- e :+ f
   | Mul : Arith -> Arith -> Arith -- e :* f
   | Int : Int -> Arith -- constant
   | Symbol : String -> Arith -- variable
```

We declare a syntax category to describe the grammar that we will be parsing.
See that we control the precedence of `:+` and `:*` by writing `syntax:50` for addition and `syntax:60` for multiplication,
indicating that multiplication binds tighter than addition (higher the number, tighter the binding).
This allows us to declare _precedence_ when defining new syntax.

```lean,ignore
declare_syntax_cat arith
syntax term : arith -- int for Arith.Int
syntax str : arith -- strings for Arith.Symbol
syntax:50  arith ":+" arith : arith -- Arith.Add
syntax:60 arith ":*" arith : arith -- Arith.Mul
syntax "(" arith ")" : arith -- bracketed expressions
```

We define the macro `fromArith%` to translate the syntax category `arith` into an `Arith` inductive value that lives in `term`:


```
-- auxiliary notation for translating `arith` into `term`
syntax "fromArith% " arith : term
```

Our macro rules perform the "obvious" translation:

```lean,ignore
macro_rules
  | `(fromArith% $s:strLit) => `(Arith.Symbol $s)
  | `(fromArith% $num:term) => `(Arith.Symbol $num)
  | `(fromArith% $x:arith :+ $y:arith ) => `(Arith.Add (fromArith% $x) (fromArith% $y))
  | `(fromArith% $x:arith :* $y:arith ) => `(Arith.Mul (fromArith% $x) (fromArith% $y))
  | `(fromArith% ($x:arith)) => `(fromArith% $x)
```
And some examples:

```lean,ignore
def foo := fromArith% ("x" :* "y") -- mul
#print foo
/-
def foo : Arith :=
Arith.Mul (Arith.Symbol "x") (Arith.Symbol "y")
-/

def bar := fromArith% ("x" :+ "y") -- add
#print bar
/-
def bar : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Symbol "y")
-/

def baz := fromArith% ("x" :+ 20) -- symbol + int
#print baz
/-
def baz : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Int 20)
-/
```

All the basic examples work. Let's check that we get precedence right as well:


```
def quux := fromArith% ("x" :+ "y" :* "z") -- multiplication binds tighter
#print quux
/-
def quux : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Mul (Arith.Symbol "y") (Arith.Symbol "z"))
-/

def quuz := fromArith% (("x" :+ "y") :* "z") -- brackets change binding order.
#print quuz
/-
def quuz : Arith :=
Arith.Mul (Arith.Add (Arith.Symbol "x") (Arith.Symbol "y")) (Arith.Symbol "z")
-/
```


Writing variables as strings, such as `"x"`  gets old; Wouldn't it be so much
prettier if we could write `x :* y`, and the macro translated this into `Arith.Mul (Arith.Symbol "x") (Arith.Mul "y")`?
We can do this, and this will be our first taste of manipulating macro variables using `x.getId`
instead of just directly evaluating them via `$x`.
We also write a macro rule for `fromArith%` that translates an identifier into
a string, using `$(Lean.quote (toString x.getId))`.  (TODO: explain what
`Lean.quote` does):

```lean,ignore
-- Have to use french quotes («arith») to refer to `arith` as
-- `arith` is a keyword after declare_syntax_cat.
-- We declare identifiers as living in the `arith` syntax category, and
-- prove an interpretation for them with `fromArith%`
syntax ident : «arith»  

macro_rules
  | `(fromArith% $x:ident) => `(Arith.Symbol $(Lean.quote (toString x.getId)))
```


Let's test and see that we can now write expressions such as `x :* y` directly instead of having to write `"x" :* "y"`:

```lean,ignore
def x_ident := fromArith% x 
#print x_ident
/-
def x_ident : Arith :=
Arith.Symbol "x"
-/

def x_plus_y : Arith := fromArith% (x :+ y)
#print x_plus_y
/-
def x_plus_y : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Symbol "y")
-/
```

We now show an unfortunate consequence of the above definitions. Suppose we want to build `(x :+ y) :+ z)`.
Since we already have defined `x_plus_y` as `x := y`, perhaps we should reuse it! Let's try:

```lean,ignore
def x_plus_y_plus_z := x_plus_y :+ z
#print x_plus_y_plus_z
/-
def x_plus_y_plus_z : Arith :=
Arith.Add (Arith.Symbol "x_plus_y") (Arith.Symbol "z")
-/
```

Whoops, that didn't work! What happened? Lean treats `x_plus_y` _itself_ as an identifier! So we need to add some syntax
to be able to "escape" the `fromArith%` context. Let's use the syntax `<[ $e:term ]>` to mean: evaluate `$e` as a real term,
not an identifier. The macro looks like follows:

```lean,ignore
syntax "<[" term "]>" : «arith» -- escape for embedding terms into `Arith`
macro_rules
  | `(fromArith% <[ $e:term ]>) => e

```

Let's try our previous example:

```lean,ignore
def x_plus_y_plus_z2 := fromArith% <[ x_plus_y ]>
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

```lean,ignore
-- example on parsing arith language via macros
inductive Arith: Type :=
   | Add : Arith -> Arith -> Arith -- e :+ f
   | Mul : Arith -> Arith -> Arith -- e :* f
   | Int : Int -> Arith -- constant
   | Symbol : String -> Arith -- variable

declare_syntax_cat arith

syntax term : arith -- int for Arith.Int
syntax str : arith -- strings for Arith.Symbol
syntax:60  arith ":+" arith : arith -- Arith.Add
syntax:70 arith ":*" arith : arith -- Arith.Mul
syntax "(" arith ")" : arith -- bracketed expressions

-- auxiliary notation for translating `arith` into `term`
syntax "fromArith% " arith : term

macro_rules
  | `(fromArith% $s:strLit) => `(Arith.Symbol $s)
  | `(fromArith% $num:term) => `(Arith.Int $num)
  | `(fromArith% $x:arith :+ $y:arith) => `(Arith.Add (fromArith% $x) (fromArith% $y))
  | `(fromArith% $x:arith :* $y:arith) => `(Arith.Mul (fromArith% $x) (fromArith% $y))
  | `(fromArith% ($x:arith)) => `(fromArith% $x)

def foo := fromArith% ("x" :* "y") -- mul
#print foo
/-
def foo : Arith :=
Arith.Mul (Arith.Symbol "x") (Arith.Symbol "y")
-/

def bar := fromArith% ("x" :+ "y") -- add
#print bar
/-
def bar : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Symbol "y")
-/

def baz := fromArith% ("x" :+ 20) -- symbol + int
#print baz
/-
def baz : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Int 20)
-/


def quux := fromArith% ("x" :+ "y" :* "z") -- precedence
#print quux
/-
def quux : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Mul (Arith.Symbol "y") (Arith.Symbol "z"))
-/

def quuz := fromArith% (("x" :+ "y") :* "z") -- brackets
#print quuz
/-
def quuz : Arith :=
Arith.Mul (Arith.Add (Arith.Symbol "x") (Arith.Symbol "y")) (Arith.Symbol "z")
-/

-- Remark: after this command, `arith` will be a "reserved" keyword, and we will have to use `«arith»`
-- to reference the `arith` syntax category

-- Have to use french quotes since `arith` is now a keyword
-- We declare identifiers as living in the `arith` syntax category.
syntax ident : «arith»  

macro_rules
  | `(fromArith% $x:ident) => `(Arith.Symbol $(Lean.quote (toString x.getId)))

def x_ident := fromArith% x 
#print x_ident
/-
def x_ident : Arith :=
Arith.Symbol "x"
-/

def x_plus_y : Arith := fromArith% (x :+ y)
#print x_plus_y
/-
def x_plus_y : Arith :=
Arith.Add (Arith.Symbol "x") (Arith.Symbol "y")
-/

def x_plus_y_plus_z := fromArith% (x_plus_y :+ z)
#print x_plus_y_plus_z
/-
def x_plus_y_plus_z : Arith :=
Arith.Add (Arith.Symbol "x_plus_y") (Arith.Symbol "z")
-/

syntax "<[" term "]>" : «arith» -- escape for embedding terms into `Arith`
 
macro_rules
  | `(fromArith% <[ $e:term ]>) => e
  


def x_plus_y_plus_z2 := fromArith% <[ x_plus_y ]>
#print x_plus_y_plus_z2
/-
def x_plus_y_plus_z2 : Arith :=
x_plus_y
-/
```

