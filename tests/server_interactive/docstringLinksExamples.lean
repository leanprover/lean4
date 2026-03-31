import Lean

/-!
This file tests that the convention for Lean block examples is correctly displayed in hovers.

Blocks that are indicated as output should be distinguished from blocks that are indicated as code
when hovers are shown. This is done by prefixing them with line comment markers.

This occurs only in hovers, so that other clients of this information can apply their own
conventions.
-/

/-!
# Ordinary Formatting
-/

/--
Does something complicated with IO that involves output.

```lean example
#eval complicatedIOProgram
```
```output
Hello!
More output
```
-/
def complicatedIOProgram : IO Unit := do
           --^ textDocument/hover
  IO.println "Hello!"
  IO.println "More output"


/-!
# Indentation
These tests check the handling of indentation for output blocks
-/

/--
Does something complicated with IO that involves output.

```lean example
#eval anotherComplicatedIOProgram
```

  ```output
  Hello!
      More output
  ```
-/
def anotherComplicatedIOProgram : IO Unit := do
           --^ textDocument/hover
  IO.println "Hello!"
  IO.println "    More output"

/--
Does something complicated with IO that involves output.

```lean example
#eval yetAnotherComplicatedIOProgram
```

  ```output
Hello!
      More output
  ```
-/
def yetAnotherComplicatedIOProgram : IO Unit := do
           --^ textDocument/hover
  IO.println "Hello!"
  IO.println "    More output"


/-!
# Programmatic Access

This test ensures that when looking up the docstring programmatically, the output blocks are not rewritten.
-/

/--
info: Does something complicated with IO that involves output.

```lean example
#eval complicatedIOProgram
```
```output
Hello!
More output
```
-/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let str ← Lean.findDocString? (← getEnv) ``complicatedIOProgram
  str.forM (IO.println ·)
