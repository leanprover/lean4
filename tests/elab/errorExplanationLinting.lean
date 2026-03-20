import Lean.ErrorExplanation
/-!
# Error Explanation Linting

Ensures that error explanation structure is correctly validated by the `register_error_explanation`
command.
-/

open Lean Meta


#guard_msgs in
/--
# Examples
## Foo
```lean broken
```
```output
```
```lean fixed
```

## Bar
```lean broken
```
-/
register_error_explanation Lean.Example2 {
  summary := ""
  sinceVersion := ""
}

#guard_msgs in
/--
Foo

# Examples
## Foo
```lean broken
```
```lean fixed
```
-/
register_error_explanation Lean.Example3 {
  summary := ""
  sinceVersion := ""
}

#guard_msgs in
/--
# Examples

# End of Examples
-/
register_error_explanation Lean.Example4 {
  summary := ""
  sinceVersion := ""
}


#guard_msgs in
/--
# Examples

## Example

```lean fixed
```
```output
```
```lean broken
```
-/
register_error_explanation Lean.Example5 {
  summary := ""
  sinceVersion := ""
}

#guard_msgs in
/--
# Examples

## Example

```lean broken
```
```lean broken
```
```output
```
```lean fixed
```
-/
register_error_explanation Lean.Example6 {
  summary := ""
  sinceVersion := ""
}

#guard_msgs in
/--
# Examples

## Example

```lean broken
```
```output
```
# End of Example
```lean fixed
```
-/
register_error_explanation Lean.Example7 {
  summary := ""
  sinceVersion := ""
}

#guard_msgs in
/--
# Examples

## Example

```lean broken_or_fixed
```
```output
```
```lean fixed
```
-/
register_error_explanation Lean.Example8 {
  summary := ""
  sinceVersion := ""
}


#guard_msgs in
/--
This is an explanation.

# Examples
## Ex

```lean broken
```
```output
```
```lean fixed
```

# Examples

Should fail
-/
register_error_explanation Lean.Example9 {
  summary := ""
  sinceVersion := ""
}

#guard_msgs in
/--
Pre-example

explanation.

```lean
-- non-example code block
```

# Examples

## First example

```lean broken
```

```output
```

```lean fixed
```

Explanation of first example.

## Second example

```lean broken
```

```output
```

```lean fixed
```

Explanation of second example.

# New Section

Foo
-/
register_error_explanation Lean.ExampleA {
  summary := ""
  sinceVersion := ""
}

/--
# Examples
## Test
```lean broken
```
```output
```
```lean fixed
```
-/
register_error_explanation Lean.WorkingExample₁ {
  summary := ""
  sinceVersion := ""
}

/--
General explanation

General explanation

# Examples (Not)

## Not an example

```lean
def foo := 32
```

# Also Not Examples

Test

# Examples

## My Example

```lean broken
```

```output
```

```lean fixed (title := "Foo")
```

Explanation of example.

-/
register_error_explanation Lean.WorkingExample₂ {
  summary := ""
  sinceVersion := ""
}

/--
Link: [`lean.someErrorName`](lean-manual://errorExplanation/lean.someErrorName)

# Examples

## Example 1
```lean broken
```
```output
```
```lean fixed
```

Link: [`lean.someErrorName`](lean-manual://errorExplanation/lean.someErrorName)

-/
register_error_explanation Lean.WorkingExample₃ {
  summary := ""
  sinceVersion := ""
}

/--

# Examples

## Nested Code Fences
````lean broken
```
````
`````output
````
`````
`````lean fixed
`````
-/
register_error_explanation Lean.WorkingExample₄ {
  summary := ""
  sinceVersion := ""
}
