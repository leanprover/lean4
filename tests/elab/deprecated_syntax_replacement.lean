import Lean

/-!
Tests the replacement alternatives of `deprecated_syntax`, which turn uses of deprecated syntax
into "Try this" suggestions.
-/

set_option linter.deprecated.syntax true

open Lean Elab Command in
/--
Elaborates `cmd` and logs its source with the edits of all resulting code action suggestions
applied.
-/
elab "#apply_suggestions " cmd:command : command => do
  let initTrees ← modifyGet fun s => (s.infoState.trees, { s with infoState.trees := {} })
  elabCommand cmd
  let trees := (← get).infoState.trees
  modify fun s => { s with infoState.trees := initTrees ++ trees }
  let fileMap ← getFileMap
  let edits := trees.foldl (init := #[]) fun edits tree =>
    tree.foldInfo (init := edits) fun _ info edits =>
      match info with
      | .ofCustomInfo { value, .. } =>
        match value.get? Meta.Tactic.TryThis.TryThisInfo with
        | some { edit, .. } =>
          edits.push (fileMap.lspPosToUtf8Pos edit.range.start,
            fileMap.lspPosToUtf8Pos edit.range.end, edit.newText)
        | none => edits
      | _ => edits
  if edits.isEmpty then return
  let some range := cmd.raw.getRange? | return
  let mut pos := range.start
  let mut result := ""
  for (start, stop, newText) in edits.qsort (·.1 < ·.1) do
    result := result ++ String.Pos.Raw.extract fileMap.source pos start ++ newText
    pos := stop
  result := result ++ String.Pos.Raw.extract fileMap.source pos range.stop
  logInfo result

/-! ## Terms -/

syntax (name := oldAdd) "old_add " term:max term:max : term
macro_rules | `(old_add $a $b) => `($a + $b)

deprecated_syntax oldAdd "use `+` instead" (since := "2026-10-19")
  | `(old_add $a $b) => `($a + $b)

-- `+` binds less tightly than `old_add`, so the replacement is parenthesized.
/--
warning: syntax 'oldAdd' has been deprecated: use `+` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵a̵d̵d̵ ̵1̵(̲1̲ ̲+̲ (2 * 3̵)̵3̲)̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: 1 + 2 * 3 : Nat
---
info: #check (1 + (2 * 3))
-/
#guard_msgs in
#apply_suggestions #check old_add 1 (2 * 3)

/-! ## Parenthesization of terms -/

syntax:max (name := oldSucc) "old_succ " term:max : term
macro_rules | `(old_succ $e) => `(Nat.succ $e)

deprecated_syntax oldSucc "use `Nat.succ` instead" (since := "2026-10-19")
  | `(old_succ $e) => `(Nat.succ $e)

-- Without parentheses, the suggestion would be `Nat.pred Nat.succ 1`.
/--
warning: syntax 'oldSucc' has been deprecated: use `Nat.succ` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵s̵u̵c̵c̵ ̵1̵(̲N̲a̲t̲.̲s̲u̲c̲c̲ ̲1̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (Nat.succ 1).pred : Nat
---
info: #check Nat.pred (Nat.succ 1)
-/
#guard_msgs in
#apply_suggestions #check Nat.pred old_succ 1

syntax:max (name := oldNeg) "old_neg " term:max : term
macro_rules | `(old_neg $e) => `(-$e)

deprecated_syntax oldNeg "use `-` instead" (since := "2026-10-19")
  | `(old_neg $e) => `(-$e)

-- `-` binds less tightly than `old_neg`.
/--
warning: syntax 'oldNeg' has been deprecated: use `-` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵n̵e̵g̵ ̵1̵(̲-̲1̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (-1).natAbs : Nat
---
info: #check Int.natAbs (-1)
-/
#guard_msgs in
#apply_suggestions #check Int.natAbs old_neg 1

syntax:65 (name := oldPlus) term:65 " +' " term:66 : term
macro_rules | `($a +' $b) => `($a + $b)

deprecated_syntax oldPlus "use `+` instead" (since := "2026-10-19")
  | `($a +' $b) => `($a + $b)

-- `+` binds exactly as tightly as `+'`, so wherever `+'` parses, `+` parses the same way.
/--
warning: syntax 'oldPlus' has been deprecated: use `+` instead

Hint: Replace the deprecated syntax:
  1 +'̵ 2

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: 1 + 2 : Nat
---
info: #check 1 + 2
-/
#guard_msgs in
#apply_suggestions #check 1 +' 2

-- Parentheses written by the user are kept and not doubled.
/--
warning: syntax 'oldPlus' has been deprecated: use `+` instead

Hint: Replace the deprecated syntax:
  1 +'̵ 2

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (1 + 2).succ : Nat
---
info: #check Nat.succ (1 + 2)
-/
#guard_msgs in
#apply_suggestions #check Nat.succ (1 +' 2)

deprecated_syntax Lean.Parser.Term.let_fun "use `have` instead" (since := "2026-10-19")
  | `(let_fun $x:ident := $v; $b) => `(have $x:ident := $v; $b)

-- Like `let_fun`, `have` extends as far to the right as possible and cannot be an argument.
/--
warning: syntax 'Lean.Parser.Term.let_fun' has been deprecated: use `have` instead

Hint: Replace the deprecated syntax:
  l̵e̵t̵_̵f̵u̵n̵h̲a̲v̲e̲ x := 1; ̵
  ̲x + 1

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: have x := 1;
x + 1 : Nat
---
info: #check have x := 1;
x + 1
-/
#guard_msgs in
#apply_suggestions #check let_fun x := 1; x + 1

syntax:max (name := oldPair) "old_pair " term:max term:max : term
macro_rules | `(old_pair $a $b) => `(($a, $b))

deprecated_syntax oldPair "use a tuple instead" (since := "2026-10-19")
  | `(old_pair $a $b) => `(($a, $b))

-- Bracketed terms bind as tightly as any syntax.
/--
warning: syntax 'oldPair' has been deprecated: use a tuple instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵p̵a̵i̵r̵ ̵1̵ ̵2̵(̲1̲,̲ ̲2̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (1, 2).fst : Nat
---
info: #check Prod.fst (1, 2)
-/
#guard_msgs in
#apply_suggestions #check Prod.fst old_pair 1 2

syntax:max (name := oldFst) "old_fst " term:max : term
macro_rules | `(old_fst $e) => `($e.1)

deprecated_syntax oldFst "use `.1` instead" (since := "2026-10-19")
  | `(old_fst $e) => `($e.1)

-- So are projections.
/--
warning: syntax 'oldFst' has been deprecated: use `.1` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵f̵s̵t̵ ̵(1, 2).̲1̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (1, 2).fst.succ : Nat
---
info: #check Nat.succ (1, 2).1
-/
#guard_msgs in
#apply_suggestions #check Nat.succ old_fst (1, 2)

syntax (name := oldZero) "old_zero" : term
macro_rules | `(old_zero) => `(Nat.zero)

deprecated_syntax oldZero "use `Nat.zero` instead" (since := "2026-10-19")
  | `(old_zero) => `(Nat.zero)

-- And identifiers.
/--
warning: syntax 'oldZero' has been deprecated: use `Nat.zero` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵N̲a̲t̲.̲zero

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: Nat.zero.succ : Nat
---
info: #check Nat.succ Nat.zero
-/
#guard_msgs in
#apply_suggestions #check Nat.succ old_zero

/-! ## Tactics -/

syntax (name := oldExact) "old_exact " term : tactic
macro_rules | `(tactic| old_exact $e) => `(tactic| exact $e)

deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $e)

/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵exact h

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (h : True) : True := by
  exact h
-/
#guard_msgs in
#apply_suggestions example (h : True) : True := by
  old_exact h

/-! ## Commands -/

syntax (name := oldCheck) "#old_check " term : command
macro_rules | `(#old_check $e) => `(#check $e)

deprecated_syntax oldCheck "use `#check` instead" (since := "2026-10-19")
  | `(#old_check $e) => `(#check $e)

/--
warning: syntax 'oldCheck' has been deprecated: use `#check` instead

Hint: Replace the deprecated syntax:
  #o̵l̵d̵_̵check Nat

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: Nat : Type
---
info: #check Nat
-/
#guard_msgs in
#apply_suggestions #old_check Nat

-- The suggestion must be part of the command's info tree, whose traversal by the unused variables
-- linter panics on nodes without context.
/--
warning: syntax 'oldCheck' has been deprecated: use `#check` instead

Hint: Replace the deprecated syntax:
  #o̵l̵d̵_̵check Nat

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: Nat : Type
-/
#guard_msgs in
set_option linter.unusedVariables true in
#old_check Nat

/-! ## Alternatives that do not apply -/

syntax (name := oldTac) "old_tac" (" with " term)? : tactic
macro_rules
  | `(tactic| old_tac) => `(tactic| trivial)
  | `(tactic| old_tac with $e) => `(tactic| exact $e)

deprecated_syntax oldTac "use `exact` instead" (since := "2026-10-19")
  | `(tactic| old_tac with $e) =>
    if e.raw.isIdent then `(tactic| exact $e) else Lean.Macro.throwError "not an identifier"

-- No alternative matches.
/--
warning: syntax 'oldTac' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : True := by old_tac

/--
warning: syntax 'oldTac' has been deprecated: use `exact` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵t̵a̵c̵ ̵w̵i̵t̵h̵ ̵h̵e̲x̲a̲c̲t̲ ̲h̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (h : True) : True := by exact h
-/
#guard_msgs in
#apply_suggestions example (h : True) : True := by old_tac with h

-- The alternative throws an error.
/--
warning: syntax 'oldTac' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : True := by old_tac with (trivial)

/-! ## Comments -/

-- A comment after the deprecated syntax stays in place and is not copied into the replacement.
/--
warning: syntax 'oldTac' has been deprecated: use `exact` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵t̵a̵c̵ ̵w̵i̵t̵h̵ ̵h̵e̲x̲a̲c̲t̲ ̲h̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (h : True) : True ∧ True := by
  constructor
  exact h -- the first goal
  trivial
-/
#guard_msgs in
#apply_suggestions example (h : True) : True ∧ True := by
  constructor
  old_tac with h -- the first goal
  trivial

/-! ## Tactics tried by several macros -/

syntax (name := oldMulti) "old_multi" (ppSpace num)? : tactic
macro_rules | `(tactic| old_multi) => `(tactic| trivial)
macro_rules | `(tactic| old_multi) => `(tactic| fail "not this one")
macro_rules | `(tactic| old_multi 1) => `(tactic| trivial)

deprecated_syntax oldMulti "use `trivial` instead" (since := "2026-10-19")
  | `(tactic| old_multi $[$_]?) => `(tactic| trivial)

-- Only the macro that succeeds reports the deprecation.
/--
warning: syntax 'oldMulti' has been deprecated: use `trivial` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵m̵u̵l̵t̵i̵t̲r̲i̲v̲i̲a̲l̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example : True := by trivial
-/
#guard_msgs in
#apply_suggestions example : True := by old_multi

/-! ## Other categories -/

syntax (name := oldConvRfl) "old_rfl" : conv
macro_rules | `(conv| old_rfl) => `(conv| rfl)

deprecated_syntax oldConvRfl "use `rfl` instead" (since := "2026-10-19")
  | `(conv| old_rfl) => `(conv| rfl)

/--
warning: syntax 'oldConvRfl' has been deprecated: use `rfl` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵rfl

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (a : Nat) : a = a := by conv => rfl
-/
#guard_msgs in
#apply_suggestions example (a : Nat) : a = a := by conv => old_rfl

syntax (name := oldBoth) "old_both" : term
attribute [tactic_parser] oldBoth
macro_rules | `(old_both) => `(42)

deprecated_syntax oldBoth "use `42` instead" (since := "2026-10-19")
  | `(old_both) => `(42)

-- The kind belongs to two categories, so it is unclear how to print the replacement.
/--
warning: syntax 'oldBoth' has been deprecated: use `42` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : Nat := old_both

/-! ## Macro-generated deprecated syntax -/

macro "wrapper" : tactic => `(tactic| old_exact trivial)

-- The fix belongs in the macro, so there is no suggestion.
/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : True := by wrapper

/-! ## Disabled linter -/

-- Neither a warning nor a code action.
#guard_msgs in
set_option linter.deprecated.syntax false in
#apply_suggestions example (h : True) : True := by old_exact h

/-! ## Hygiene -/

syntax (name := oldConst) "old_const " term:max : term

macro_rules | `(old_const $e) => `(fun _ => $e)

deprecated_syntax oldConst "use `fun` instead" (since := "2026-10-19")
  | `(old_const $e) => `(fun x => Nat.succ $e)

-- Identifiers introduced by the alternative are printed without macro scopes.
/--
warning: syntax 'oldConst' has been deprecated: use `fun` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵c̵o̵n̵s̵t̵ ̵1̵(̲f̲u̲n̲ ̲x̲ ̲=̲>̲ ̲N̲a̲t̲.̲s̲u̲c̲c̲ ̲1̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example : Nat → Nat := (fun x => Nat.succ 1)
-/
#guard_msgs in
#apply_suggestions example : Nat → Nat := old_const 1

syntax (name := oldHyg) "old_hyg" : term
macro_rules | `(old_hyg) => `(fun _ => 0)

deprecated_syntax oldHyg "use `fun` instead" (since := "2026-10-19")
  | `(old_hyg) => do
    let y ← Lean.Macro.addMacroScope `y
    `(fun $(Lean.mkIdent y) => 0)

-- Identifiers created from a name with macro scopes stay inaccessible.
/--
warning: syntax 'oldHyg' has been deprecated: use `fun` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵h̵y̵g̵(̲f̲u̲n̲ ̲y̲✝̲ ̲=̲>̲ ̲0̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example : Nat → Nat := (fun y✝ => 0)
-/
#guard_msgs in
#apply_suggestions example : Nat → Nat := old_hyg

/-! ## Identifier patterns -/

syntax (name := oldNum) "old_num" : term
macro_rules | `(old_num) => `(42)

def oldNumReplacement : Lean.Macro := fun _ => `(42)

deprecated_syntax oldNum "use `42` instead" (since := "2026-10-19")
  | stx => oldNumReplacement stx

/--
warning: syntax 'oldNum' has been deprecated: use `42` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵n̵u̵m̵4̲2̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example : Nat := 42
-/
#guard_msgs in
#apply_suggestions example : Nat := old_num

/-! ## Core syntax -/

deprecated_syntax Lean.Parser.Tactic.rwaAtLegacyLocation
  "use `rw [...] at ... <;> assumption` instead" (since := "2026-08-27")
  | `(tactic| rwa $rws:rwRuleSeq $loc:location) =>
    `(tactic| rw $rws:rwRuleSeq $loc:location <;> assumption)

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Hint: Replace the deprecated syntax:
  r̵w̵a̵r̲w̲ [h] at * ̲<̲;̲>̲ ̲a̲s̲s̲u̲m̲p̲t̲i̲o̲n̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (a b : Nat) (h : a = b) (h' : a = 0) : b = 0 := by
  rw [h] at * <;> assumption
-/
#guard_msgs in
#apply_suggestions example (a b : Nat) (h : a = b) (h' : a = 0) : b = 0 := by
  rwa [h] at *

/-! ## Redeprecation without alternatives removes the replacement -/

deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-19")

/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example (h : True) : True := by old_exact h

/-! ## Invalid alternatives -/

/--
error: invalid deprecated_syntax alternative, unexpected syntax node kind `Lean.Parser.Tactic.exact`
-/
#guard_msgs in
deprecated_syntax oldExact (since := "2026-10-19")
  | `(tactic| exact $e) => `(tactic| exact $e)

/--
error: invalid deprecated_syntax alternative, expected a syntax quotation pattern or a single identifier pattern
-/
#guard_msgs in
deprecated_syntax oldExact (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $e)
  | _ => `(tactic| trivial)

-- An alternative that fails to elaborate does not register a replacement.
/--
error: failed to synthesize instance of type class
  HAdd (Lean.TSyntax `term) Nat (Lean.TSyntax `term)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
deprecated_syntax oldExact (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $(e + 1))

/--
warning: syntax 'oldExact' has been deprecated

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example (h : True) : True := by old_exact h
