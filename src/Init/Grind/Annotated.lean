/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Init.Notation

public section
namespace Lean.Parser.Command

/--
`grind_annotated "YYYY-MM-DD"` marks the current file as having been manually annotated for `grind`.

When the LibrarySuggestion framework is called with `caller := "grind"` (as happens when using
`grind +suggestions`), theorems from grind-annotated files are excluded from premise selection.
This is because these files have already been manually reviewed and annotated with appropriate
`@[grind]` attributes.

The date argument (in YYYY-MM-DD format) records when the file was annotated. This is currently
informational only, but may be used in the future to detect files that have been significantly
modified since annotation and may need re-review.

Example:
```
grind_annotated "2025-01-15"
```

This command should typically appear near the top of a file, after imports.
-/
syntax (name := grindAnnotated) "grind_annotated" str : command

end Lean.Parser.Command
