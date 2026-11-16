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

/-!
Simp theorems whose discrimination tree keys contain a deprecated declaration are not reported,
since `simp` only uses them on terms that mention the deprecated declaration, which is already
reported.
-/

@[deprecated replacementDef (since := "2025-01-01")]
def oldDef (n : Nat) : Nat := n + 1

#guard_msgs in
@[simp, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_eq (n : Nat) : oldDef n = replacementDef n := rfl

-- The key only needs to contain the deprecated declaration, not start with it.
#guard_msgs in
@[simp, deprecated "no replacement" (since := "2025-01-01")]
theorem succ_oldDef (n : Nat) : (oldDef n).succ = replacementDef n + 1 := rfl

-- For `←`, the keys come from the right-hand side.
#guard_msgs in
@[simp ←, deprecated "no replacement" (since := "2025-01-01")]
theorem eq_oldDef (n : Nat) : n + 2 = oldDef (n + 1) := rfl

/--
warning: `oldDef_eq'` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[s̵i̵m̵p̵ ̵←̵,̵ ̵deprecated "no replacement" (since := "2025-01-01")]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[simp ←, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_eq' (n : Nat) : oldDef (n + 1) = n + 2 := rfl

-- Each simp theorem created from a conjunction needs to contain a deprecated declaration.
#guard_msgs in
@[simp, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_and (n : Nat) : oldDef n = replacementDef n ∧ oldDef 0 = 1 := ⟨rfl, rfl⟩

/--
warning: `oldDef_and'` is deprecated, but the `[simp]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[s̵i̵m̵p̵,̵ ̵deprecated "no replacement" (since := "2025-01-01")]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[simp, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_and' (n : Nat) : oldDef n = replacementDef n ∧ replacementDef 0 = 1 := ⟨rfl, rfl⟩

-- Deprecated definitions are only unfolded where they occur.
#guard_msgs in
@[simp, deprecated replacementDef (since := "2025-01-01")]
def oldDef2 (n : Nat) : Nat := n + 1

-- A declaration that is not deprecated is not reported, whatever its keys contain. Only the use
-- of the deprecated declaration in its statement is.
/--
warning: `oldDef` has been deprecated: Use `replacementDef` instead

Hint: Replace the deprecated name:
  o̵l̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
@[simp] theorem oldDef_eq_notDeprecated (n : Nat) : oldDef n = replacementDef n := rfl

-- The exemption also applies when the declaration is deprecated in the same `attribute` command.
set_option linter.deprecated false in
theorem oldDef_eq_later (n : Nat) : oldDef n = replacementDef n := rfl

#guard_msgs in
attribute [simp, deprecated "no replacement" (since := "2025-01-01")] oldDef_eq_later

/-!
The same applies to `grind`, whose theorems are only activated once all symbols of their patterns
occur in the goal.
-/

#guard_msgs in
@[grind =, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_eq2 (n : Nat) : oldDef n = replacementDef n := rfl

#guard_msgs in
@[grind ., deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_eq3 (n : Nat) : oldDef n = replacementDef n := rfl

/--
warning: `oldDef_eq4` is deprecated, but the `[grind]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  @[g̵r̵i̵n̵d ̵=̵_̵,̵ ̵d̵eprecated "no replacement" (since := "2025-01-01")]

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
@[grind =_, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_eq4 (n : Nat) : oldDef n = replacementDef n := rfl

#guard_msgs in
@[grind →, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_fwd (n : Nat) (h : oldDef n = 1) : n = 0 := by simp only [oldDef] at h; omega

#guard_msgs in
@[grind inj, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_inj : Function.Injective oldDef := fun _ _ h => by simp only [oldDef] at h; omega

#guard_msgs in
@[grind norm, deprecated "no replacement" (since := "2025-01-01")]
theorem oldDef_norm (n : Nat) : oldDef n = replacementDef n := rfl

#guard_msgs in
@[grind, deprecated replacementDef (since := "2025-01-01")]
def oldDef3 (n : Nat) : Nat := n + 1

#guard_msgs in
@[grind unfold, deprecated replacementDef (since := "2025-01-01")]
def oldDef4 (n : Nat) : Nat := n + 1

@[deprecated "no replacement" (since := "2025-01-01")]
inductive OldPred : Nat → Prop
  | zero : OldPred 0

#guard_msgs in
attribute [grind intro] OldPred

/--
warning: `OldPred` is deprecated, but the `[grind]` attribute lets automation use it without a deprecation warning

Hint: Remove the attribute:
  a̵t̵t̵r̵i̵b̵u̵t̵e̵ ̵[̵g̵r̵i̵n̵d̵ ̵c̵a̵s̵e̵s̵]̵ ̵O̵l̵d̵P̵r̵e̵d̵

Note: Removing the attribute may break proofs that rely on it. If it needs to be kept for now, this warning can be disabled with `set_option linter.deprecated.automationAttr false in`
-/
#guard_msgs in
attribute [grind cases] OldPred

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
