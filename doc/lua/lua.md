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
assert(tostring(x1) == "x::1")
assert(x1 ~= name("x::1"))  -- x1 is not equal to the string x::1
assert(x1 == name("x", 1))

local o = name("lean", "pp", "colors")
-- The previous construct is syntax sugar for the following expression
assert(o == name(name(name("lean"), "pp"), "colors"))

assert(x < y) -- '<' is a total order on hierarchical names

local h = x:hash() -- retrieve the hash code for 'x'
assert(h ~= y:hash())
```
