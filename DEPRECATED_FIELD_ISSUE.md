# Pre-filled issue: deprecation does not fire on structure-field provision

Copy the section below into a new issue at https://github.com/leanprover/lean4/issues/new
(title on the first line, body underneath). Everything above the horizontal rule is a note to
you and is not part of the issue.

Suggested labels: `bug`, or `RFC` if you'd rather frame it as a feature request.
The MWE was checked on `4.35.0-pre` (recent `master`); adjust the version line if needed.

---

**Title:** `@[deprecated]` on a structure field's projection does not warn when the field is provided by name in an anonymous-constructor / `where` block

**Body:**

## Summary

`@[deprecated]` on a structure/class field deprecates the *projection* constant, so it warns on
*reads* of the field, but it does **not** warn when the field is *provided by name* in an anonymous
constructor `{ … }` or a `where` block. This makes it impossible to fully deprecate a field name:
the construction side, which is exactly where instance/structure authors need the migration nudge,
stays silent.

## Minimal working example

```lean
structure Point where
  x : Nat
  y : Nat

attribute [deprecated Point.x (since := "2026-01-01")] Point.y

-- (1) Provide the deprecated field `y` by name in an anonymous constructor / `where`.
def p₁ : Point := { x := 1, y := 2 }
def p₂ : Point where
  x := 1
  y := 2

-- (2) Reference the deprecated projection `Point.y`.
example : Nat := Point.y p₁
```

## Expected behavior

The mentions of `y` in `(1)` — the field labels in `{ x := 1, y := 2 }` and in the `where` block —
should emit a deprecation warning, just like the projection reference in `(2)` does.

## Actual behavior

Only `(2)` warns:

```
warning: `Point.y` has been deprecated: Use `Point.x` instead
```

`(1)` produces no warning at all. The two definitions `p₁` and `p₂` compile silently.

## Why this matters

A structure/class field cannot be renamed backward-compatibly with a warning-driven migration path.
Concretely, renaming a class field (e.g. a `WP.wpTrans → WP.trans` rename) can be made
non-breaking by keeping both names as fields with mutual default values:

```lean
class C (α : Type) where
  trans   : α → α := wpTrans
  wpTrans : α → α := trans      -- deprecated alias
attribute [deprecated C.trans (since := "…")] C.wpTrans
```

Instances that construct with the old field name (`instance … where wpTrans := …`) keep compiling,
and reads of `C.wpTrans` warn — but there is no way to nudge those instance authors to migrate,
because their `where wpTrans := …` never warns.

## No existing mechanism covers field-label provision

None of the current deprecation mechanisms warn when a field is provided by name in `{ … }` /
`where`. The anonymous-constructor elaborator resolves each field label against the structure's real
fields directly, so it never consults deprecation:

- `@[deprecated]` on the projection (`Point.y` above) fires on a *constant reference*, i.e. reads;
  the field label is not a constant reference.
- `@[deprecated_arg]` (#13011) fires on named *arguments* of an explicit call; the field label does
  not go through named-argument elaboration. Applied to the constructor, it warns for
  `S.mk (old := 5)` but the `{ … }` / `where` forms hard-error instead:

  ```lean
  structure S where
    new : Nat
  attribute [deprecated_arg old new (since := "2026-01-01")] S.mk

  def s0 : S := S.mk (old := 5)   -- warning: parameter `old` of `S.mk` has been deprecated, use `new` instead
  def s1 : S := { old := 5 }      -- error: `old` is not a field of structure `S`; Fields missing: `new`
  def s2 : S where
    old := 5                       -- error: `old` is not a field of structure `S`; Fields missing: `new`
  ```

- `deprecated_syntax` deprecates a *syntax kind*, not a particular identifier used as a field label.

## Versions

- Lean (version 4.35.0-pre, `x86_64-unknown-linux-gnu`, Release), built from a recent `master`
  (4.36.0 development cycle).
