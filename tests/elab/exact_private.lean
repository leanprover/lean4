module

/-!
# Tests for `exact?` with private declarations

This tests that `exact?` can suggest private theorems.

## Accessibility rules for private declarations in `exact?`:
- Local private declarations (defined in current file/module): always suggested
- Imported private declarations:
  - In module system with `import all`: suggested
  - In module system without `import all`: not suggested
  - Outside module system: not suggested
-/

-- Test that exact? suggests local private declarations
axiom P : Prop
private axiom p : P

/--
info: Try this:
  [apply] exact p
-/
#guard_msgs in
example : P := by exact?
