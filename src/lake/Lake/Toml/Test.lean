
/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Toml.Grammar
import Lean.Elab.ElabRules

/-!
# TOML Tests
-/

namespace Lake.Toml.Test

/-!
## Test Utilities
-/

section
open Lean Parser Elab Command

def runParserFn (p : ParserFn) (input : String) (fileName := "<string>") : IO Syntax := do
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    throw <| .userError <| s.toErrorMsg ictx
  else if input.atEnd s.pos then
    return s.stxStack.back
  else
    throw <| .userError <| (s.mkError "end of input").toErrorMsg ictx

def runParser (p : Parser) (input : String) (fileName := "<string>") : IO Syntax := do
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext input fileName
  let s := p.fn.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    throw <| .userError <| s.toErrorMsg ictx
  else if input.atEnd s.pos then
    return s.stxStack.back
  else
    throw <| .userError <| (s.mkError "end of input").toErrorMsg ictx

@[scoped command_parser] def hashParse : Parser := leading_parser
  "#parse" >> ident >>
  strAtom "```" (trailingFn := newlineFn) >> checkLinebreakBefore >>
  parserOfStack 1 >> checkLinebreakBefore >> strAtom "```" (trailingFn := whitespace)

@[command_elab hashParse] def noElab : CommandElab :=
  fun _ _ => pure ()

end

/-!
## README Example

TOML syntax example from the [README][1].

[1]: https://github.com/toml-lang/toml/blob/1.0.0/README.md#example
-/

#parse toml ```
# This is a TOML document.

title = "TOML Example"

[owner]
name = "Tom Preston-Werner"
dob = 1979-05-27T07:32:00-08:00 # First class dates

[database]
server = "192.168.1.1"
ports = [ 8001, 8001, 8002 ]
connection_max = 5000
enabled = true

[servers]

  # Indentation (tabs and/or spaces) is allowed but not required
  [servers.alpha]
  ip = "10.0.0.1"
  dc = "eqdc10"

  [servers.beta]
  ip = "10.0.0.2"
  dc = "eqdc10"

[clients]
data = [ ["gamma", "delta"], [1, 2] ]

# Line breaks are OK when inside arrays
hosts = [
  "alpha",
  "omega"
]
```

/-!
## Specification Examples

TOML syntax examples from the [specification](https://toml.io/en/v1.0.0).
-/

#parse toml ```
# -----------------
# Comment
# -----------------

# This is a full-line comment
key = "value"  # This is a comment at the end of a line
another = "# This is not a comment"

# -----------------
# Key/Value Pair
# -----------------

key = "value"
# key = # INVALID
#first = "Tom" last = "Preston-Werner" # INVALID

# -----------------
# Keys
# -----------------

key = "value"
bare_key = "value"
bare-key = "value"
1234 = "value"

"127.0.0.1" = "value"
"character encoding" = "value"
"ʎǝʞ" = "value"
'key2' = "value"
'quoted "value"' = "value"

# = "no key name"  # INVALID
"" = "blank"     # VALID but discouraged
'' = 'blank'     # VALID but discouraged

name = "Orange"
physical.color = "orange"
physical.shape = "round"
site."google.com" = true

fruit.name = "banana"     # this is best practice
fruit. color = "yellow"    # same as fruit.color
fruit . flavor = "banana"   # same as fruit.flavor

3.14159 = "pi"

# -----------------
# String
# -----------------

str = "I'm a string. \"You can quote me\". Name\tJos\u00E9\nLocation\tSF."

str1 = """
Roses are red
Violets are blue"""

# On a Unix system, the above multi-line string will most likely be the same as:
str2 = "Roses are red\nViolets are blue"

# On a Windows system, it will most likely be equivalent to:
str3 = "Roses are red\r\nViolets are blue"

# The following strings are byte-for-byte equivalent:
str1 = "The quick brown fox jumps over the lazy dog."

str2 = """
The quick brown \


  fox jumps over \
    the lazy dog."""

str3 = """\
       The quick brown \
       fox jumps over \
       the lazy dog.\
       """

str4 = """Here are two quotation marks: "". Simple enough."""
# str5 = """Here are three quotation marks: """."""  # INVALID
str5 = """Here are three quotation marks: ""\"."""
str6 = """Here are fifteen quotation marks: ""\"""\"""\"""\"""\"."""

# "This," she said, "is just a pointless statement."
str7 = """"This," she said, "is just a pointless statement.""""

# What you see is what you get.
winpath  = 'C:\Users\nodejs\templates'
winpath2 = '\\ServerX\admin$\system32\'
quoted   = 'Tom "Dubs" Preston-Werner'
regex    = '<\i\c*\s*>'

regex2 = '''I [dw]on't need \d{2} apples'''
lines  = '''
The first newline is
trimmed in raw strings.
   All other whitespace
   is preserved.
'''

quot15 = '''Here are fifteen quotation marks: """""""""""""""'''

# apos15 = '''Here are fifteen apostrophes: ''''''''''''''''''  # INVALID
apos15 = "Here are fifteen apostrophes: '''''''''''''''"

# 'That,' she said, 'is still pointless.'
str = ''''That,' she said, 'is still pointless.''''

# -----------------
# Integer
# -----------------

int1 = +99
int2 = 42
int3 = 0
int4 = -17

int5 = 1_000
int6 = 5_349_221
int7 = 53_49_221  # Indian number system grouping
int8 = 1_2_3_4_5  # VALID but discouraged

# hexadecimal with prefix `0x`
hex1 = 0xDEADBEEF
hex2 = 0xdeadbeef
hex3 = 0xdead_beef

# octal with prefix `0o`
oct1 = 0o01234567
oct2 = 0o755 # useful for Unix file permissions

# binary with prefix `0b`
bin1 = 0b11010110

# -----------------
# Float
# -----------------

# fractional
flt1 = +1.0
flt2 = 3.1415
flt3 = -0.01

# exponent
flt4 = 5e+22
flt5 = 1e06
flt6 = -2E-2

# both
flt7 = 6.626e-34

# INVALID FLOATS
#invalid_float_1 = .7
#invalid_float_2 = 7.
#invalid_float_3 = 3.e+20

flt8 = 224_617.445_991_228

# infinity
sf1 = inf  # positive infinity
sf2 = +inf # positive infinity
sf3 = -inf # negative infinity

# not a number
sf4 = nan  # actual sNaN/qNaN encoding is implementation-specific
sf5 = +nan # same as `nan`
sf6 = -nan # valid, actual encoding is implementation-specific

# -----------------
# Boolean
# -----------------

bool1 = true
bool2 = false

# -----------------
# Date-Time
# -----------------

odt1 = 1979-05-27T07:32:00Z
odt2 = 1979-05-27T00:32:00-07:00
odt3 = 1979-05-27T00:32:00.999999-07:00

odt4 = 1979-05-27 07:32:00Z

ldt1 = 1979-05-27T07:32:00
ldt2 = 1979-05-27T00:32:00.999999

ld1 = 1979-05-27

lt1 = 07:32:00
lt2 = 00:32:00.999999

# -----------------
# Array
# -----------------

integers = [ 1, 2, 3 ]
colors = [ "red", "yellow", "green" ]
nested_arrays_of_ints = [ [ 1, 2 ], [3, 4, 5] ]
nested_mixed_array = [ [ 1, 2 ], ["a", "b", "c"] ]
string_array = [ "all", 'strings', """are the same""", '''type''' ]

# Mixed-type arrays are allowed
numbers = [ 0.1, 0.2, 0.5, 1, 2, 5 ]
contributors = [
  "Foo Bar <foo@example.com>",
  { name = "Baz Qux", email = "bazqux@example.com", url = "https://example.com/bazqux" }
]

integers2 = [
  1, 2, 3
]

integers3 = [
  1,
  2, # this is ok
]

# -----------------
# Table
# -----------------

[table]

[table-1]
key1 = "some string"
key2 = 123

[table-2]
key1 = "another string"
key2 = 456

[dog."tater.man"]
type.name = "pug"

[a.b.c]            # this is best practice
[ d.e.f ]          # same as [d.e.f]
[ g .  h  . i ]    # same as [g.h.i]
[ j . "ʞ" . 'l' ]  # same as [j."ʞ".'l']

# -----------------
# Inline Table
# -----------------

name = { first = "Tom", last = "Preston-Werner" }
point = { x = 1, y = 2 }
animal = { type.name = "pug" }

points = [ { x = 1, y = 2, z = 3 },
           { x = 7, y = 8, z = 9 },
           { x = 2, y = 4, z = 8 } ]

# -----------------
# Array of Tables
# -----------------

[[products]]
name = "Hammer"
sku = 738594937

[[products]]  # empty table within the array

[[products]]
name = "Nail"
sku = 284758393

[[fruits]]
name = "apple"

[fruits.physical]  # subtable
color = "red"
shape = "round"

[[fruits.varieties]]  # nested array of tables
name = "red delicious"

[[fruits.varieties]]
name = "granny smith"
```
