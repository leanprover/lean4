/-!
Tests that deprecation warnings for leading-dot identifiers (`.deprecatedCtor`), generalized field
notation (`t.deprecatedDef`, `t |>.deprecatedDef`), and structure projections
(`s.deprecatedField`) offer a hint to switch to the replacement.
-/

set_option linter.deprecated true

structure T where
  n : Nat

def T.replacementMkDef (n : Nat) : T := ⟨n⟩
@[deprecated T.replacementMkDef (since := "2025-01-01")] def T.deprecatedMkDef (n : Nat) : T := ⟨n⟩

def T.replacementDef (t : T) : Nat := t.n
@[deprecated T.replacementDef (since := "2025-01-01")] def T.deprecatedDef (t : T) : Nat := t.n

/-! Leading-dot identifiers -/

/--
warning: `T.deprecatedMkDef` has been deprecated: Use `T.replacementMkDef` instead

Hint: Replace the deprecated name:
  .̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵M̵k̵D̵e̵f̵.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲M̲k̲D̲e̲f̲
-/
#guard_msgs in
example : T := .deprecatedMkDef 1

/--
warning: `T.deprecatedMkDef` has been deprecated: Use `T.replacementMkDef` instead

Hint: Replace the deprecated name:
  .̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵M̵k̵D̵e̵f̵.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲M̲k̲D̲e̲f̲
-/
#guard_msgs in
example : T := @.deprecatedMkDef 1

/--
warning: `T.deprecatedMkDef` has been deprecated: Use `T.replacementMkDef` instead

Hint: Replace the deprecated name:
  .̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵M̵k̵D̵e̵f̵.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲M̲k̲D̲e̲f̲
-/
#guard_msgs in
example : Nat → T := .deprecatedMkDef

def otherMkDef (n : Nat) : T := ⟨n⟩
@[deprecated otherMkDef (since := "2025-01-01")] def T.deprecatedMkDef' (n : Nat) : T := ⟨n⟩

-- The replacement is in a different namespace, so the hint uses its name.
/--
warning: `T.deprecatedMkDef'` has been deprecated: Use `otherMkDef` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.deprecatedMkDef'` to `otherMkDef x`).

Hint: Replace the deprecated name:
  .̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵M̵k̵D̵e̵f̵'̵o̲t̲h̲e̲r̲M̲k̲D̲e̲f̲
-/
#guard_msgs in
example : T := .deprecatedMkDef' 1

inductive L where
  | replacementCtor
  | deprecatedCtor
attribute [deprecated L.replacementCtor (since := "2025-01-01")] L.deprecatedCtor

/--
warning: `L.deprecatedCtor` has been deprecated: Use `L.replacementCtor` instead

Hint: Replace the deprecated name:
  .̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example : L := .deprecatedCtor

/--
warning: `L.deprecatedCtor` has been deprecated: Use `L.replacementCtor` instead

Hint: Replace the deprecated name:
  .̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example (k : L) : Nat := match k with | .deprecatedCtor => 0 | _ => 1

/-! Generalized field notation -/

/--
warning: `T.deprecatedDef` has been deprecated: Use `T.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example (t : T) : Nat := t.deprecatedDef

/--
warning: `T.deprecatedDef` has been deprecated: Use `T.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example (t : T) : Nat := t |>.deprecatedDef

/--
warning: `T.deprecatedDef` has been deprecated: Use `T.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example : T → Nat := (· |>.deprecatedDef)

/--
warning: `T.deprecatedDef` has been deprecated: Use `T.replacementDef` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵D̵e̵f̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example (t : T) : Nat := (t).deprecatedDef

def otherDef (t : T) : Nat := t.n
@[deprecated otherDef (since := "2025-01-01")] def T.deprecatedDef' (t : T) : Nat := t.n

-- The replacement is in a different namespace, so field notation cannot be kept.
/--
warning: `T.deprecatedDef'` has been deprecated: Use `otherDef` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.deprecatedDef'` to `otherDef x`).
-/
#guard_msgs in
example (t : T) : Nat := t.deprecatedDef'

/-! Structure projections -/

structure S where
  replacementField : Nat
  deprecatedField : Nat
attribute [deprecated S.replacementField (since := "2025-01-01")] S.deprecatedField

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (s : S) : Nat := s.deprecatedField

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (s : S) : Nat := (s).deprecatedField

/--
warning: `S.deprecatedField` has been deprecated: Use `S.replacementField` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵F̵i̵e̵l̵d̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲F̲i̲e̲l̲d̲
-/
#guard_msgs in
example (s : S) : Nat := s |>.deprecatedField
