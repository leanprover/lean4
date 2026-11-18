/-!
Tests that patterns report deprecated constructors exactly once, do not report pattern variables
that happen to share the name of a deprecated constant, and explain why no hint is offered when the
replacement cannot be used in a pattern.
-/

set_option linter.deprecated true

def replacementDef : Nat := 1
@[deprecated replacementDef (since := "2025-01-01")] def deprecatedDef : Nat := 1

/-! Pattern variables and binders that happen to share the name of a deprecated definition. -/

#guard_msgs in
example (n : Nat) : Nat := match n with | 0 => 0 | deprecatedDef => deprecatedDef + 1

#guard_msgs in
example : Nat → Nat := fun | 0 => 0 | deprecatedDef => deprecatedDef + 1

#guard_msgs in
example : Nat → Nat := fun (deprecatedDef) => deprecatedDef + 1

#guard_msgs in
example (p : Nat × Nat) : Nat := let ⟨deprecatedDef, _⟩ := p; deprecatedDef

#guard_msgs in
example (n : Nat) : Nat := match n with | .succ deprecatedDef => deprecatedDef | 0 => 0

#guard_msgs in
example (o : Option Nat) : Nat := if let some deprecatedDef := o then deprecatedDef else 0

#guard_msgs in
example : Nat × Nat → Nat := fun (deprecatedDef, _) => deprecatedDef

#guard_msgs in
def doLet (p : Nat × Nat) : Id Nat := do
  let (deprecatedDef, _) := p
  return deprecatedDef

#guard_msgs in
def doFor (xs : List (Nat × Nat)) : Id Nat := do
  let mut s := 0
  for (deprecatedDef, _) in xs do
    s := s + deprecatedDef
  return s

/-! Deprecated constructors in patterns are reported exactly once. -/

inductive L where
  | replacementCtor
  | deprecatedCtor
attribute [deprecated L.replacementCtor (since := "2025-01-01")] L.deprecatedCtor

inductive I where
  | replacementCtor (n : Nat)
  | deprecatedCtor (n : Nat)
attribute [deprecated I.replacementCtor (since := "2025-01-01")] I.deprecatedCtor

/--
warning: `L.deprecatedCtor` has been deprecated: Use `L.replacementCtor` instead

Hint: Replace the deprecated name:
  L̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵L̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example (k : L) : Nat := match k with | L.deprecatedCtor => 0 | _ => 1

/--
warning: `L.deprecatedCtor` has been deprecated: Use `L.replacementCtor` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
open L in
example (k : L) : Nat := match k with | deprecatedCtor => 0 | _ => 1

/--
warning: `I.deprecatedCtor` has been deprecated: Use `I.replacementCtor` instead

Hint: Replace the deprecated name:
  I̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵I̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example (k : I) : Nat := match k with | I.deprecatedCtor n => n | _ => 1

/--
warning: `I.deprecatedCtor` has been deprecated: Use `I.replacementCtor` instead

Hint: Replace the deprecated name:
  I̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵I̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
example : I → Nat := fun | I.deprecatedCtor n => n | _ => 1

/--
warning: `L.deprecatedCtor` has been deprecated: Use `L.replacementCtor` instead

Hint: Replace the deprecated name:
  L̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵L̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
def doMatch (k : L) : Id Nat := do
  match k with
  | L.deprecatedCtor => return 0
  | _ => return 1

/--
warning: `I.deprecatedCtor` has been deprecated: Use `I.replacementCtor` instead

Hint: Replace the deprecated name:
  I̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵I̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲C̲t̲o̲r̲
-/
#guard_msgs in
def doIfLet (k : I) : Id Nat := do
  if let I.deprecatedCtor n := k then return n
  return 0

/-!
No replacement hint in a pattern when the replacement is neither a constructor nor
`@[match_pattern]`, since the replacement cannot be used in a pattern. The warning explains this
instead, including that the unqualified replacement would be a catch-all pattern variable.
-/

inductive M where
  | otherCtor
  | deprecatedCtor
abbrev M.replacementDef : M := .deprecatedCtor
attribute [deprecated M.replacementDef (since := "2025-01-01")] M.deprecatedCtor

/--
warning: `M.deprecatedCtor` has been deprecated: Use `M.replacementDef` instead

Note: `M.replacementDef` is neither a constructor nor a `@[match_pattern]` definition, so it cannot be used in this pattern. Written as `replacementDef`, it would instead be a new pattern variable that matches every value.
-/
#guard_msgs in
open M in
example (k : M) : Nat := match k with | deprecatedCtor => 0 | _ => 1

-- Outside of patterns, the replacement can be used as usual.
/--
warning: `M.deprecatedCtor` has been deprecated: Use `M.replacementDef` instead

Hint: Replace the deprecated name:
  M̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵M̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example : M := M.deprecatedCtor

-- A `@[match_pattern]` replacement can be used in patterns.
inductive P where
  | otherCtor
  | deprecatedCtor
@[match_pattern] abbrev P.replacementDef : P := .deprecatedCtor
attribute [deprecated P.replacementDef (since := "2025-01-01")] P.deprecatedCtor

/--
warning: `P.deprecatedCtor` has been deprecated: Use `P.replacementDef` instead

Hint: Replace the deprecated name:
  P̵.̵d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵C̵t̵o̵r̵P̲.̲r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲D̲e̲f̲
-/
#guard_msgs in
example (k : P) : Nat := match k with | P.deprecatedCtor => 0 | _ => 1
