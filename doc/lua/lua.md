# Lua API documentation

We the [Lua](http://www.lua.org) script language to customize and
extend [Lean](http://leanprover.net). This
[link](http://www.lua.org/docs.html) is a good starting point for
learning Lua. In this document, we focus on the Lean specific APIs.
Most of Lean components are exposed in the Lua API.

**Remark:** the script [md2lua.sh](md2lua.sh) extracts the Lua code
examples from the `*.md` documentation files in this directory.

## Hierarchical names

In Lean, we use _hierarchical names_ for identifying configuration
options, constants, and kernel objects. A hierarchical name is
essentially a list of strings and integers.
The following example demonstrates how to create and manipulate
hierarchical names using the Lua API.

```lua
local x = name("x")    -- create a simple hierarchical name
local y = name("y")
-- In Lua, 'assert(p)' succeeds if 'p' does not evaluate to false (or nil)
assert(x == name("x")) -- test if 'x' is equal to 'name("x")'
assert(x ~= y)         -- '~=' is the not equal operator in Lua
assert(x ~= "x")

assert(is_name(x)) -- test whether argument is a hierarchical name or not.
assert(not is_name("x"))

local x1 = name(x, 1) -- x1 is a name composed of the string "x" and number 1
assert(tostring(x1) == "x.1")
assert(x1 ~= name("x.1"))  -- x1 is not equal to the string x.1
assert(x1 == name("x", 1))

local o = name("lean", "pp", "colors")
-- The previous construct is syntax sugar for the following expression
assert(o == name(name(name("lean"), "pp"), "colors"))

assert(x < y) -- '<' is a total order on hierarchical names

local h = x:hash() -- retrieve the hash code for 'x'
assert(h ~= y:hash())
```

## Lua tables

Tables are the only mutable, non-atomic type of data in Lua.  Tables
are used to implement mappings, arrays, lists, objects, etc. Here is a
small examples demonstrating how to use Lua tables:

```lua
local t = {}    -- create an empty table
t["x"]  = 10    -- insert the entry "x" -> 10
t.x     = 20    -- syntax-sugar for t["x"] = 20
t["y"]  = 30    -- insert the entry "y" -> 30
assert(t["x"] == 20)
local p = { x = 10, y = 20 } -- create a table with two entries
assert(p.x == 10)
assert(p["x"] == 10)
assert(p.y == 20)
assert(p["y"] == 20)
```

Arrays are implemented by indexing tables with integers.
The arrays don't have a fixed size and grow dynamically.
The arrays in Lua usually start at index 1. The Lua libraries
use this convention. The following example initializes
an array with 100 elements.

```lua
local a = {}    -- new array
for i=1, 100 do
    a[i] = 0
end
local b = {2, 4, 6, 8, 10} -- create an array with 5 elements
assert(#b == 5)    -- array has 5 elements
assert(b[1] == 2)
assert(b[2] == 4)
```
In Lua, we cannot provide custom hash and equality functions to tables.
So, we cannot effectively use Lua tables to implement mappings where
the keys are Lean hierarchical names, expressions, etc.
The following example demonstrates the issue.

```lua
local m  = {} -- create empty table
local a  = name("a")
m[a]     = 10 -- map the hierarchical name 'a' to 10
assert(m[a] == 10)
local a1 = name("a")
assert(a == a1)      -- 'a' and 'a1' are the same hierarchical name
assert(m[a1] == nil) -- 'a1' is not a key in the mapping 'm'
assert(m[a]  == 10)
-- 'a' and 'a1' are two instances of the same object
-- Lua tables assume that different instances are not equal
```

## Red-black tree maps

In Lean, we provide red-black tree maps for implementing mappings where the keys are
Lean objects such as hierarchical names. The maps are implemented on
top of [red-black tree data structure](http://en.wikipedia.org/wiki/Red%E2%80%93black_tree).
We can also use Lua atomic data types as keys in these maps.
However, we should not mix different types in the same map.
The Lean map assumes that `<` is a total order on the
keys inserted in the map.

```lua
local m = rb_map() -- create an empty red-black tree map
assert(is_rb_map(m))
assert(#m == 0)
local a  = name("a", 1)
local a1 = name("a", 1)
m:insert(a, 10)          -- add the entry 'a.1' -> 10
assert(m:find(a1) == 10)
m:insert(name("b"), 20)
assert(#m == 2)
m:erase(a)               -- remove entry with key 'a.1'
assert(m:find(a) == nil)
assert(not m:contains(a))
assert(#m == 1)
m:insert(name("c"), 30)
m:for_each(              -- traverse the entries in the map
    function(k, v)       -- executing the given function
        print(k, v)
    end
)
local m2 = m:copy()      -- the maps are copied in constant time
assert(#m2 == #m)
m2:insert(name("b", 2), 40)
assert(#m2 == #m + 1)
```

## Multiple precision numerals

We expose [GMP](http://gmplib.org/) (GNU Multiple precision arithmetic
library) in Lua. Internally, Lean uses multiple precision numerals for
representing expressing containing numerals.
In Lua, we can create multiple precision integers (_mpz_) and multiple
precision rationals (_mpq_). The following example demonstrates how to
use `mpz` and `mpq` numerals.

```lua
local ten = mpz(10) -- create the mpz numeral 10.
assert(is_mpz(ten)) -- test whether 'ten' is a mpz numeral or not
assert(not is_mpz(10))
local big = mpz("100000000000000000000000") -- create a mpz numeral from a string
-- The operators +, -, *, /, ^, <, <=, >, >=, ==, ~=
-- The operators +, -, *, /, ^ accept mixed mpz and Lua native types
assert(ten + 1 == mpz(11))
-- In Lua, objects of different types are always different
-- So, the mpz number 10 is different from the native Lua numeral 10
assert(mpz(10) ~= 10)
assert(mpz(3) / 2 == mpz(1))
-- The second argument of ^ must be a non-negative Lua numeral
assert(mpz(10) ^ 100 > mpz("1000000000000000000000000"))
assert(mpz(3) * mpz("1000000000000000000000") == mpz("3000000000000000000000"))
assert(mpz(4) + "10" == mpz(14))
local q1 = mpq(10) -- create the mpq numeral 10
local q2 = q1 / 3  -- create the mpq numeral 10/3
assert(q2 == mpq("10/3"))
local q3 = mpq(0.25) -- create the mpq numeral 1/4
assert(q3 == mpq(1)/4)
assert(is_mpq(q3)) -- test whether 'q3' is a mpq numeral or not
assert(not is_mpq(mpz(10))) -- mpz numerals are not mpq
assert(ten == mpz(10))
local q4 = mpq(ten) -- convert the mpz numeral 'ten' into a mpq numeral
assert(is_mpq(q4))
assert(mpq(1)/3 + mpq(2)/3 == mpq(1))
assert(mpq(0.5)^5 == mpq("1/32"))
assert(mpq(1)/2 > mpq("1/3"))
```

## S-expressions

In Lean, we use Lisp-like non-mutable S-expressions as a basis for
building configuration options, statistics, formatting objects, and
other structured objects. S-expressions can be atomic values (nil, strings,
hierarchical names, integers, doubles, Booleans, and multiple precision
integers and rationals), or pairs (aka _cons-cell_).
The following example demonstrates how to create S-expressions using Lua.

```lua
local s = sexpr(1, 2) -- Create a pair containing the atomic values 1 and 2
assert(is_sexpr(s))   -- 's' is a pair
assert(s:is_cons())   -- 's' is a cons-cell/pair
assert(s:head():is_atom())   -- the 'head' is an atomic S-expression
assert(s:head() == sexpr(1)) -- the 'head' of 's' is the atomic S-expression 1
assert(s:tail() == sexpr(2)) -- the 'head' of 's' is the atomic S-expression 2
s = sexpr(1, 2, 3, nil) -- Create a 'list' containing 1, 2 and 3
assert(s:length() == 3)
assert(s:head() == sexpr(1))
assert(s:tail() == sexpr(2, 3, nil))
assert(s:head():is_int())      -- the 'head' is an integer
assert(s:head():to_int() == 1) -- return the integer stored in the 'head' of 's'
local h, t = s:fields()        -- return the 'head' and 'tail' of s
assert(h == sexpr(1))
```

The following example demonstrates how to test the kind of and extract
the value stored in atomic S-expressions.

```lua
assert(sexpr(1):is_int())
assert(sexpr(1):to_int() == 1)
assert(sexpr(true):is_bool())
assert(sexpr(false):to_bool() == false)
assert(sexpr("hello"):is_string())
assert(sexpr("hello"):to_string() == "hello")
assert(sexpr(name("n", 1)):is_name())
assert(sexpr(name("n", 1)):to_name() == name("n", 1))
assert(sexpr(mpz(10)):is_mpz())
assert(sexpr(mpz(10)):to_mpz() == mpz(10))
assert(sexpr(mpq(3)/2):is_mpq())
assert(sexpr(mpq(3)/2):to_mpq() == mpq(6)/4)
```
We can also use the method `fields` to extract the value stored
in atomic S-expressions. It is more convenient than using
the `to_*` methods.

```lua
assert(sexpr(10):fields() == 10)
assert(sexpr("hello"):fields() == "hello")
```

The `to_*` methods raise an error is the argument does not match
the expected type. Remark: in Lua, we catch errors using
the builtin function [`pcall`](http://pgl.yoyo.org/luai/i/pcall) (aka _protected call_).

```lua
local s = sexpr(10)
local ok, ex = pcall(function() s:to_string() end)
assert(not ok)
-- 'ex' is a Lean exception
assert(is_exception(ex))
```

We say an S-expression `s` is a _list_ iff `s` is a pair, and the
`tail` is nil or a list. So, every _list_ is a pair, but not every
pair is a list.

```lua
assert(sexpr(1, 2):is_cons()) -- The S-expression is a pair
assert(not sexpr(1, 2):is_list()) -- This pair is not a list
assert(sexpr(1, nil):is_list())   -- List with one element
assert(sexpr(1, 2, nil):is_list()) -- List with two elements
-- The expression sexpr(1, 2, nil) is syntax-sugar
-- for sexpr(1, sexpr(2, nil))
assert(sexpr(1, 2, nil) == sexpr(1, sexpr(2, nil)))
-- The methond 'length' returns the length of the list
assert(sexpr(1, 2, nil):length() == 2)
```

We can encode trees using S-expressions. The following example
demonstrates how to write a simple recursive function that
collects all leaves (aka atomic values) stored in a S-expression
tree.

```lua
function collect(S)
    -- We store the result in a Lua table
    local result = {}
    function loop(S)
        if S:is_cons() then
            loop(S:head())
            loop(S:tail())
        elseif not S:is_nil() then
            result[#result + 1] = S:fields()
        end
    end
    loop(S)
    return result
end
-- Create a simple tree
local tree = sexpr(sexpr(1, 5), sexpr(sexpr(4, 3), 5))
local leaves = collect(tree) -- store the leaves in a Lua table
assert(#leaves == 5)
assert(leaves[1] == 1)
assert(leaves[2] == 5)
assert(leaves[3] == 4)
```

## Options

Lean components can be configured used _options_ objects.  The options
can be explicitly provided or read from a global variable. An options
object is a non-mutable value based on S-expressions.
An options object is essentially a list of pairs, where each pair
is a hierarchical name and a value. The following example demonstrates
how to create options objects using Lua.

```lua
-- Create an options set containing the entries
--   pp.colors  -> false,
--   pp.unicode -> false
local o1 = options(name("pp", "colors"), false, name("pp", "unicode"), false)
assert(is_options(o1))
print(o1)
-- The same example using syntax-sugar for hierarchical names.
-- The Lean-Lua API will automatically convert Lua arrays into hierarchical names.
local o2 = options({"pp", "colors"}, false, {"pp", "unicode"}, false)
print(o2)
-- An error is raised if the option is not known.
local ok, ex = pcall(function() options({"pp", "foo"}, true) end)
assert(not ok)
assert(ex:what():find("unknown option 'pp.foo'"))
```

Options objects are non-mutable values. The method `update` returns a new
updates options object.

```lua
local o1 = options() -- create the empty options
assert(o1:empty())
local o2 = o1:update({'pp', 'colors'}, true)
assert(o1:empty())
assert(not o2:empty())
assert(o2:size() == 1)
assert(o2:get({'pp', 'colors'}) == true)
assert(o2:get{'pp', 'colors'} == true)
assert(o2:contains{'pp', 'colors'})
assert(not o2:contains{'pp', 'unicode'})
-- We can provide a default value for 'get'.
-- The default value is used if the options object does
-- not contain the key.
assert(o2:get({'pp', 'width'}) == 0)
assert(o2:get({'pp', 'width'}, 10) == 10)
assert(o2:get({'pp', 'width'}, 20) == 20)
local o3 = o2:update({'pp', 'width'}, 100)
assert(o3:get({'pp', 'width'}) == 100)
assert(o3:get({'pp', 'width'}, 1) == 100)
assert(o3:get({'pp', 'width'}, 20) == 100)
```

The functions `get_options` and `set_options` get/set the global
options object. For example, the global options object is used
by the `print` method.

```lua
local o = options({'pp', 'unicode'}, false)
set_options(o)
assert(get_options():contains{'pp', 'unicode'})
```

# Universe levels

Lean supports universe polymorphism. That is, declaration in Lean can
be parametrized by one or more universe level parameters.
The declarations can then be instantiated with universe level
expressions. In the standard Lean front-end, universe levels can be
omitted, and the Lean elaborator (tries) to infer them automatically
for users. In this section, we describe the API for creating and using
universe level expressions.

In Lean, we have a hierarchy of universes: `Type.{0}` : `Type.{1}` :
`Type.{2}`, ...
We do not assume our universes are cumulative (like Coq).
In Lean, when we create an empty environment, we can specify whether
`Type.{0}` is impredicative or not. The idea is to be able to use
`Type.{0}` to represent the universe of Propositions.

In Lean, we have the following kinds of universe level expression:
- `Zero`         : the universe level expression for representing `Type.{0}`.
- `Succ(l)`      : the successor of universe level `l`.
- `Max(l1, l2)`  : the maximum of levels `l1` and `l2`.
- `IMax(l1, l2)` : the "impredicative" maximum. It is defined as
  `IMax(x, y) = Zero` if `y` is `Zero`, and `Max(x, y)` otherwise.
- `Param(n)`     : a universe level parameter named `n`.
- `Global(n)`    : a global universe level named `n`.
- `Meta(n)`      : a meta universe level named `n`. Meta universe
  levels are used to identify placeholders that must be automatically
  constructed by Lean.

The following example demonstrates how to create universe level
expressions using Lua.

```lua
local zero = level()    -- Create level Zero
assert(is_level(zero))  -- zero is a level expression
assert(zero:is_zero())
local one  = zero + 1   -- Create level One
assert(one ~= 1)        -- level one is not the constant 1
-- We can also use the API mk_level_succ instead of +1
local two  = mk_level_succ(one) -- Create level Two
assert(two == one+1)
assert(two:is_succ())   -- two is of the kind: successor
assert(two:succ_of() == one)  -- it is the successor of one
local u = mk_global_univ("u") -- u is a reference to global universe level "u"
assert(u:is_global())
assert(u:id() == name("u"))   -- Retrieve u's name
local l = mk_param_univ("l")  -- l is a reference to a universe level parameter
assert(l:is_param())
assert(l:id() == name("l"))
assert(l:id() ~= "l")         -- The names are not strings, but hierarchical names
assert(l:kind() == level_kind.Param)
local m = mk_meta_univ("m")   -- Create a meta universe level named "m"
assert(m:is_meta())
assert(m:id() == name("m"))
print(max_univ(l, u))         -- Create level expression Max(l, u)
assert(max_univ(l, u):is_max())
-- The max_univ API applies basic coercions automatically
assert(max_univ("l", 1) == max_univ(l, one))
assert(max_univ("l", 1, u) == max_univ(l, max_univ(one, u)))
-- The max_univ API applies basic simplifications automatically
assert(max_univ(l, l) == l)
assert(max_univ(l, zero) == l)
assert(max_univ(one, zero) == one)
print(imax_univ(l, u))       -- Create level expression IMax(l, u)
assert(imax_univ(l, u):is_imax())
-- The imax_univ API also applies basic coercions automatically
assert(imax_univ(1, "l") == imax_univ(one, l))
-- The imax_univ API applies basic simplifications automatically
assert(imax_univ(l, l) == l)
assert(imax_univ(l, zero) == zero)
-- It "knows" that u+1 can never be zero
assert(imax_univ(l, u+1) == max_univ(l, u+1))
assert(imax_univ(zero, one) == one)
assert(imax_univ(one, zero) == zero)
-- The methods lhs and rhs deconstruct max and imax expressions
assert(max_univ(l, u):lhs() == l)
assert(imax_univ(l, u):rhs() == u)
-- The method is_not_zero if there if for all assignments
-- of the parameters, globals and meta levels, the resultant
-- level expression is different from zero.
assert((l+1):is_not_zero())
assert(not l:is_not_zero())
assert(max_univ(l+1, u):is_not_zero())
-- The method instantiate replaces parameters with level expressions
assert(max_univ(l, u):instantiate({"l"}, {two}) == max_univ(two, u))
local l1 = mk_param_univ("l1")
assert(max_univ(l, l1):instantiate({"l", "l1"}, {two, u+1}) == max_univ(two, u+1))
-- The method has_meta returns true, if the given level expression
-- contains meta levels
assert(max_univ(m, l):has_meta())
assert(not max_univ(u, l):has_meta())
-- The is_eqp method checks for pointer equality
local e1 = max_univ(l, u)
local e2 = max_univ(l, u)
assert(e1 == e2)
local e3 = e1
-- e1 and e3 are references to the same level expression.
assert(e1:is_eqp(e3))
```

In the previous example, we learned that functions such as `max_univ`
apply basic simplifications automatically. However, they do not put
the level expressions in any normal form. We can use the method
`normalize` for that. The normalization procedure is also use to
implement the method `is_equivalent` that returns true when two level
expressions are equivalent. The Lua API also contains the method
`is_geq` that can be used to check whether a level expression
represents a universe bigger than or equal another one.

```lua
local zero = level()
local l = mk_param_univ("l")
local u = mk_global_univ("u")
assert(max_univ(l, 1, u+1):is_equivalent(max_univ(u+1, 1, l)))
local e1 = max_univ(l, u+1)+1
assert(e1:normalize() == max_univ(l+1, u+2))
-- norm is syntax sugar for normalize
assert(e1:norm() == max_univ(l+1, u+2))
assert(e1:is_geq(l))
assert(e1:is_geq(e1))
assert(e1:is_geq(zero))
assert(e1:is_geq(u+2))
assert(e1:is_geq(max_univ(l, u)))
```

We say a universe level is _explicit_ iff it is of the form
`succ^k(zero)`

```lua
local zero = level()
assert(zero:is_explicit())
local two  = zero+2
assert(two:is_explicit())
local l    = mk_param_univ("l")
assert(not l:is_explicit())
```

The Lua dictionary `level_kind` contains the id for all universe level
kinds.

```lua
local zero = level()
local one  = zero+1
local l    = mk_param_univ("l")
local u    = mk_global_univ("u")
local m    = mk_meta_univ("m")
local e1   = max_univ(l, u)
local e2   = imax_univ(m, l)
assert(zero:kind() == level_kind.Zero)
assert(one:kind()  == level_kind.Succ)
assert(l:kind()    == level_kind.Param)
assert(u:kind()    == level_kind.Global)
assert(m:kind()    == level_kind.Meta)
assert(e1:kind()   == level_kind.Max)
assert(e2:kind()   == level_kind.IMax)
```

# Expressions

In Lean, we have the following kind of expressions: constants,
function applications, variables, lambdas, dependent function spaces
(aka Pis), let expressions, and sorts (aka Type).
There are three additional kinds of auxiliary
expressions: local constants, metavariables, and macros.

## Constants

Constants are essentially references to declarations in the
environment. We can create a variable using

```lua
local f = mk_constant("f")
local a = Const("a")       -- Const is an alias for mk_constant
assert(is_expr(f))         -- f is an expression
assert(f:is_constant())    -- f is a constant
```
Lean supports universe polymorphism. When we define a constant,
theorem or axiom, we can use universe level parameters.
Thus, if a declaration `g` has two universe level parameters,
we instantiate them when we create a reference to `g`.

```lua
local zero = level()
local one  = zero+1
local g01  = mk_constant("g", {zero, one})
```

The command `mk_constant` automatically applies coercions to level
expressions. A numeral `n` is automatically converted into
`level()+n`, and a string `s` into `mk_param_univ(s)`.

```lua
local g1l = mk_constant("g", {1, "l"})
```

The method `data()` retrieves the name and universe levels of a
constant.

```lua
local gl1 = mk_constant("g", {"l", 1})
assert(gl1:is_constant())
local n, ls = gl1:data()
assert(n == name("g"))
assert(#ls == 2)
assert(ls:head() == mk_param_univ("l"))
assert(ls:tail():head() == level()+1)
```

## Function applications

In Lean, the expression `f t` is a function application, where `f` is
a function that is applied to `t`.

```lua
local f = Const("f")
local t = Const("t")
local a = f(t)        -- Creates the term `f t`
assert(is_expr(a))
assert(a:is_app())
```

The method `data()` retrieves the function and argument of an
application. The methods `fn()` and `arg()` retrieve the function
and argument respectively.

```lua
local f = Const("f")
local t = Const("t")
local a = f(t)
assert(a:fn()  == f)
assert(a:arg() == t)
local g, b = a:data()
assert(g == f)
assert(b == t)
```
As usual, we write `f t s` to denote the expression
`((f t) s)`. The Lua API provides a similar convenience.

```lua
local f = Const("f")
local t = Const("t")
local s = Const("s")
local a = f(t, s)
assert(a:fn() == f(t))
assert(a:fn():fn() == f)
assert(a:fn():arg() == t)
assert(a:arg() == s)
```

## Variables

Variables are references to local declarations in lambda and Pi
expressions. The variables are represented using
[de Bruijn indices](http://en.wikipedia.org/wiki/De_Bruijn_index).

```lua
local x = mk_var(0)
local y = Var(1)    -- Var is an alias for mk_var
assert(is_expr(x))
assert(x:is_var())
assert(x:data() == 0)
assert(y:data() == 1)
```

## Lambda abstractions

Lambda abstraction is a converse operation to function
application. Given a variable `x`, a type `A`, and a term `t` that may or
may not contain `x`, one can construct the so-called lambda abstraction
`fun x : A, t`, or using unicode notation `λ x : A, t`.
There are many APIs for creating lambda abstractions in the Lua API.
The most basic one is `mk_lambda(x, A, t)`, where `x` is a string or
hierarchical name, and `A` and `t` are expressions.

```lua
local x  = Var(0)
local A  = Const("A")
local id = mk_lambda("x", A, x) -- create the identity function
assert(is_expr(id))
assert(id:is_lambda())
```

As usual, the method `data()` retrieves the "fields" of a lambda
abstraction.

```lua
-- id is the identity function defined above.
local y, B, v = id:data()
assert(y == name("x"))
assert(B == A)
assert(v == Var(0))
```

We say a variable is _free_ if it is not bound by any lambda (or Pi)
abstraction. We say an expression is _closed_ if it does not contain
free variables. The method `closed()` return `true` iff the expression
is closed.

```lua
local f  = Const("f")
local N  = Const("N")
assert(not f(Var(0)):closed())
local l1 = mk_lambda("x", N, f(Var(0)))
assert(l1:closed())
local l2 = mk_lambda("x", N, f(Var(1)))
assert(not l2:closed())
```

The method `has_free_var(i)` return `true` if the expression contains
the free variable `i`.

```lua
local f  = Const("f")
local N  = Const("N")
assert(f(Var(0)):has_free_var(0))
assert(not f(Var(0)):has_free_var(1))
local l1 = mk_lambda("x", N, f(Var(0)))
assert(not l1:has_free_var(0))
local l2 = mk_lambda("x", N, f(Var(1)))
assert(l2:has_free_var(0))
assert(not l2:has_free_var(1))
```

The de Bruijn indices can be lifted and lowered using the methods
`lift_free_vars` and `lower_free_vars`.

```lua
local f  = Const("f")
local N  = Const("N")
assert(f(Var(0)):lift_free_vars(1) == f(Var(1)))
assert(f(Var(0)):lift_free_vars(2) == f(Var(2)))
-- lift the free variables >= 2 by 3
assert(f(Var(0), Var(2)):lift_free_vars(2, 3) == f(Var(0), Var(5)))

assert(f(Var(1)):lower_free_vars(1) == f(Var(0)))
assert(f(Var(2)):lower_free_vars(1) == f(Var(1)))
-- lower the free variables >= 2 by 1
assert(f(Var(0), Var(2)):lower_free_vars(2, 1) ==
       f(Var(0), Var(1)))
```

It is not convenient to create complicated lambda abstractions using
de Bruijn indices. It is usually a very error-prone task.
To simplify the creation of lambda abstractions, Lean provides local constants.
A local constant is essentially a pair name and expression, where the
expression represents the type of the local constant.
The API `Fun(c, b)` automatically replace the local constant `c` in `b` with
the variable 0. It does all necessary adjustments when `b` contains nested
lambda abstractions. The API also provides `Fun(c_1, ..., c_n, b)` as
syntax-sugar for `Fun(c_1, ..., Fun(c_n, b)...)`.

```lua
local N   = Const("N")
local f   = Const("f")
local c_1 = Local("c_1", N)
local c_2 = Local("c_2", N)
local c_3 = Local("c_3", N)
assert(Fun(c_1, f(c_1)) == mk_lambda("c_1", N, f(Var(0))))
assert(Fun(c_1, c_2, f(c_1, c_2)) ==
       mk_lambda("c_1", N, mk_lambda("c_2", N, f(Var(1), Var(0)))))
assert(Fun(c_1, c_2, f(c_1, Fun(c_3, f(c_2, c_3)))) ==
       mk_lambda("c_1", N, mk_lambda("c_2", N,
           f(Var(1), mk_lambda("c_3", N, f(Var(1), Var(0)))))))
````

Local constants can be annotated with `hints` for the Lean _elaborator_.
For example, we can say a binder is an _implicit argument_, and
must be inferred automatically by the elaborator.
These annotations are irrelevant from the kernel's point of view,
and they are just "propagated" by the Lean type checker.
The other annotations are explained later in the Section describing
the elaboration engine.

```lua
local b = binder_info(true)
assert(is_binder_info(b))
assert(b:is_implicit())
local N   = Const("N")
local f   = Const("f")
local c1  = Local("c1", N, b)
local c2  = Local("c2", N)
-- Create the expression
--    fun {c1 : N} (c2 : N), (f c1 c2)
-- In Lean, curly braces are used to denote
-- implicit arguments
local l   = Fun(c1, c2, f(c1, c2))
local x, T, B, bi = l:data()
assert(x == name("c1"))
assert(T == N)
assert(B == Fun(c2, f(Var(1), c2)))
assert(bi:is_implicit())
local y, T, C, bi2 = B:data()
assert(not bi2:is_implicit())
```
