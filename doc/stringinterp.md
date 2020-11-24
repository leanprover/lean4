# String interpolation

The `s!` prefix identifies a string literal as an interpolated string.
An interpolated string is a string literal that might contain interpolation expressions.
When an interpolated string is resolved to a result string, items with interpolation expressions are
replaced by the string representations of the expression results. The polymorphic method `toString` is used
to convert the value into a string.

String interpolation provides a more readable and convenient syntax to create formatted strings than
a string composite formatting feature. The following example uses both features to produce the same output:

```lean
def name := "John"
def age  := 28

#eval IO.println s!"Hello, {name}! Are you {age} years old?"

#eval IO.println ("Hello, " ++ name ++ "! Are you " ++ toString age ++ " years old?")

-- `println! <interpolated-string>` is a macro for `IO.println s!<interpolated-string>`
#eval println! "Hello, {name}! Are you {age} years old?"
```

# Structure of an interpolated string

To identify a string literal as an interpolated string, prepend it with `s!`.
Terms inside braces `{}` are ordinary expressions whose type implements the type class `ToString`.
To include a curly brace `{` in your interpolated string, you must escape it using `\{`.
You can nest interpolated strings inside interpolated strings.

```lean
def vals := [1, 2, 3]

#eval IO.println s!"\{ vals := {vals} }"

#eval IO.println s!"variables: {vals.map (fun i => s!"x_{i}")}"
```

# `ToString` instances

You can define a `ToString` instance for your own datatypes.

```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString : Person -> String
    | { name := n, age := v } => s!"\{ name := {n}, age := {v} }"

def person1 : Person := {
  name := "John"
  age  := 28
}

#eval println! "person1: {person1}"
```
