import Lean

import Std.Internal.Parsec

open Lean Meta

/-- error: Example 'Bar' is malformed: Expected a(n) `output` code block -/
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
register_error_explanation Example {
  summary := ""
  sinceVersion := ""
}

/--
error: Example 'Foo' is malformed: Expected a(n) `output` code block, but found a(n) `lean` one
-/
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
register_error_explanation Example {
  summary := "hi"
  sinceVersion := "4.0.0"
}

/-- error: Expected level-2 header for an example section, but found `# End of Examples` -/
#guard_msgs in
/--
# Examples

# End of Examples
-/
register_error_explanation Example {
  summary := ""
  sinceVersion := ""
}


/--
error: Example 'Example' is malformed: Expected a(n) broken `lean` code block, but found a(n) fixed `lean` one
-/
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
register_error_explanation Example {
  summary := ""
  sinceVersion := ""
}

/--
error: Example 'Example' is malformed: Expected a(n) `output` code block, but found a(n) `lean` one
-/
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
register_error_explanation Example {
  summary := ""
  sinceVersion := ""
}

/-- error: Example 'Example' is malformed: Expected a(n) fixed `lean` code block -/
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
register_error_explanation Example {
  summary := ""
  sinceVersion := ""
}

/--
error: Example 'Example' is malformed: Invalid code block info string `lean broken_or_fixed`: offset 20: invalid attribute broken_or_fixed
-/
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
register_error_explanation Example {
  summary := ""
  sinceVersion := ""
}


/-- error: Expected level-2 header for an example section, but found `# Examples` -/
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
register_error_explanation Example {
  summary := ""
  sinceVersion := ""
}

/-- error: Expected level-2 header for an example section, but found `# New Section` -/
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
register_error_explanation Example {
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
register_error_explanation WorkingExample₁ {
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
register_error_explanation WorkingExample₂ {
  summary := ""
  sinceVersion := ""
}

-- TODO: check extracted code blocks in working examples
