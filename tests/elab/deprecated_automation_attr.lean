/-!
Tests that tagging a deprecated declaration with an attribute that adds it to a set used by
automation, such as `simp` or `grind`, is reported, with a hint to remove the attribute.
-/

set_option linter.deprecated true

def replacementDef (n : Nat) : Nat := n + 1

theorem replacementThm (n : Nat) : replacementDef n = n + 1 := rfl

/-! Declaration attributes -/

/--
warning: `deprecatedThm` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[s̵i̵m̵p̵,̵ ̵deprecated replacementThm (since := "2025-01-01")]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[simp, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedThm2` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[deprecated replacementThm (since := "2025-01-01"),̵ ̵s̵i̵m̵p̵ ̵←̵]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[deprecated replacementThm (since := "2025-01-01"), simp ←]
theorem deprecatedThm2 (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedThm3` is deprecated, but the `[grind]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[g̵r̵i̵n̵d ̵=̵,̵ ̵d̵eprecated replacementThm (since := "2025-01-01")]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[grind =, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm3 (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedThm4` is deprecated, but the `[seval]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[l̵o̵c̵a̵l̵ ̵s̵e̵v̵a̵l̵,̵ ̵deprecated replacementThm (since := "2025-01-01"), simp]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
---
warning: `deprecatedThm4` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[local seval, deprecated replacementThm (since := "2025-01-01"),̵ ̵s̵i̵m̵p̵]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[local seval, deprecated replacementThm (since := "2025-01-01"), simp]
theorem deprecatedThm4 (n : Nat) : replacementDef n = n + 1 := rfl

-- Other attributes are not reported.
#guard_msgs in
@[inline, deprecated replacementDef (since := "2025-01-01")]
def deprecatedDef (n : Nat) : Nat := n + 1

-- Declarations that are not deprecated are not reported.
#guard_msgs in
@[simp, grind =]
theorem otherThm (n : Nat) : replacementDef n = n + 1 := rfl

-- Nothing is reported if the linter is disabled.
#guard_msgs in
set_option linter.deprecated false in
@[simp, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm5 (n : Nat) : replacementDef n = n + 1 := rfl

-- The warning can be disabled on its own, for when the attribute needs to be kept.
#guard_msgs in
set_option linter.deprecated.automationAttr false in
@[simp, deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm7 (n : Nat) : replacementDef n = n + 1 := rfl

/-! The `attribute` command -/

@[deprecated replacementThm (since := "2025-01-01")]
theorem deprecatedThm6 (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `deprecatedThm6` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  a̵t̵t̵r̵i̵b̵u̵t̵e̵ ̵[̵s̵i̵m̵p̵]̵ ̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵6̵

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
attribute [simp] deprecatedThm6

/--
warning: `deprecatedThm6` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  attribute [s̵i̵m̵p̵,̵ ̵grind =] deprecatedThm6

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
---
warning: `deprecatedThm6` is deprecated, but the `[grind]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  attribute [simp,̵ ̵g̵r̵i̵n̵d̵ ̵=̵] deprecatedThm6

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
attribute [simp, grind =] deprecatedThm6

/--
warning: `deprecatedThm6` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  attribute [simp] d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵T̵h̵m̵6̵ ̵otherThm

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
attribute [simp] deprecatedThm6 otherThm

-- Removing either the attribute or the declaration would also remove something else.
/-- warning: `deprecatedThm6` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
attribute [simp, -grind] deprecatedThm6 otherThm

theorem otherThm2 (n : Nat) : replacementDef n = n + 1 := rfl

/--
warning: `otherThm2` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  attribute [s̵i̵m̵p̵,̵ ̵deprecated replacementThm (since := "2025-01-01")] otherThm2

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
attribute [simp, deprecated replacementThm (since := "2025-01-01")] otherThm2

-- Disabling the warning does not fall back to the generic deprecation warning.
#guard_msgs in
set_option linter.deprecated.automationAttr false in
attribute [simp] deprecatedThm6

-- Erasing the attribute is not reported.
#guard_msgs in
attribute [-simp] deprecatedThm6

-- Deprecating a declaration that already has the attribute is not reported.
@[simp] theorem otherThm3 (n : Nat) : replacementDef n = n + 1 := rfl

#guard_msgs in
attribute [deprecated replacementThm (since := "2025-01-01")] otherThm3
