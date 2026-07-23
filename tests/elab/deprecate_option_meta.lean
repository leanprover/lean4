import Lean.Data.Options

/-!
Options are deprecated with a `@[deprecated]` attribute on `register_option`, which warns on
meta-code references to the option. `register_option` mirrors the attribute's replacement name,
message, and `since` into the option's internal `deprecation?` field so that `set_option` also warns
(the `set_option`
side requires the option to be registered in an imported module; see `deprecatedOptions.lean`).

The `deprecation?` field is an internal implementation detail: setting it directly on
`register_option` is an error.
-/

open Lean

-- The harness runs with `linter.all` disabled; re-enable the deprecation linter explicitly.
set_option linter.deprecated true

-- A `@[deprecated]` attribute makes meta-code references to the option warn.
@[deprecated "use `myOwn.newOpt` instead" (since := "2026-01-15")]
register_option myOwn.deprecatedOpt : Bool := { defValue := true, descr := "an option" }

/-- warning: `myOwn.deprecatedOpt` has been deprecated: use `myOwn.newOpt` instead -/
#guard_msgs in
def usesDeprecatedOpt (o : Options) : Bool := myOwn.deprecatedOpt.get o

-- A non-deprecated option does not warn.
register_option myOwn.plainOpt : Nat := { defValue := 3, descr := "a plain option" }

#guard_msgs in
def usesPlainOpt (o : Options) : Nat := myOwn.plainOpt.get o

-- A `@[deprecated <name>]` attribute names a replacement option instead of a custom message.
register_option myOwn.newOpt : Bool := { defValue := true, descr := "the replacement option" }

@[deprecated myOwn.newOpt (since := "2026-01-15")]
register_option myOwn.deprecatedByName : Bool := { defValue := true, descr := "an option" }

/-- warning: `myOwn.deprecatedByName` has been deprecated: Use `myOwn.newOpt` instead -/
#guard_msgs in
def usesDeprecatedByName (o : Options) : Bool := myOwn.deprecatedByName.get o

-- Setting `deprecation?` directly is an error: it is internal and populated from the attribute.
/--
error: do not set the `deprecation?` field directly; it is an internal implementation detail. Deprecate the option with a `@[deprecated "..." (since := "...")]` attribute instead
-/
#guard_msgs in
register_option myOwn.badFieldOnly : Bool :=
  { defValue := true, descr := "d", deprecation? := some { since := "2026-01-15" } }

-- Providing both the attribute and the field is also an error: the field is redundant.
/--
error: remove the `deprecation?` field: it is populated automatically from the option's `@[deprecated]` attribute
-/
#guard_msgs in
@[deprecated "msg" (since := "2026-01-15")]
register_option myOwn.badBoth : Bool :=
  { defValue := true, descr := "d", deprecation? := some { since := "2026-01-15" } }
