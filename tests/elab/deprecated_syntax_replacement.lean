import Lean

/-!
Tests the replacement alternatives of `deprecated_syntax`, which turn uses of deprecated syntax
into "Try this" suggestions.
-/

set_option linter.deprecated.syntax true

open Lean Elab Command in
/--
Elaborates `cmd` and logs its source with the edits of all resulting code action suggestions
applied. With `!`, also parses and elaborates the edited command.
-/
elab "#apply_suggestions " check?:("!")? cmd:command : command => do
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
  if check?.isSome then
    let edited ← ofExcept <| Parser.runParserCategory (← getEnv) `command result
    withReader (fun ctx => { ctx with fileMap := FileMap.ofString result }) do
      elabCommand edited

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

/-! ## Token boundaries -/

syntax:75 (name := oldBoundaryNeg) "old_boundary_neg " term:75 : term
macro_rules | `(old_boundary_neg $e) => `(-$e)

deprecated_syntax oldBoundaryNeg (since := "2026-10-22")
  | `(old_boundary_neg $e) => `(-$e)

-- The two minus signs must not become a line comment.
/-- info: example : Int := - -1 -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := -old_boundary_neg 1

/-- info: example : Int := (- -1) -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := (-old_boundary_neg 1)

/-- info: example : Int := - -1 -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := - old_boundary_neg 1

-- Adjacent tokens that remain distinct do not need extra whitespace.
/-- info: example : Int := (-1) -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := (old_boundary_neg 1)

/-- info: example (α : Int) : Int := - -α -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example (α : Int) : Int := -old_boundary_neg α

/-- info: example : Int := 1/ -1 -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := 1/old_boundary_neg 1

-- Lexical context may start inside a string or comment.
/-- info: example (n : Int) : String := s!"value: {- -n}" -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example (n : Int) : String := s!"value: {-old_boundary_neg n}"

/-- info: example : Int := /- comment -/- -1 -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := /- comment -/-old_boundary_neg 1

-- Trivia after the deprecated syntax stays in place and already separates the replacement.
/-- info: example : Int := (-1/- comment -/) -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := (old_boundary_neg 1/- comment -/)

section

-- The current token table must be used, including tokens spanning more than two characters.
local prefix:75 "+++" => Neg.neg
local prefix:75 "+++-" => id

/-- info: example : Int := +++ -1 -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Int := +++old_boundary_neg 1

-- A replacement can also collide with the token after it.
local syntax:max (name := oldBoundaryUnit) "old_boundary_unit" : term
local macro_rules | `(old_boundary_unit) => `(())
local postfix:max ")!" => id
local postfix:max "))!" => id

deprecated_syntax oldBoundaryUnit (since := "2026-10-22")
  | `(old_boundary_unit) => `(())

/-- info: example : Unit := () )! -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : Unit := old_boundary_unit)!

local syntax:max (name := oldBoundaryId) "old_boundary_id%" term:max "%" : term
local macro_rules | `(old_boundary_id% $e %) => `($e)

deprecated_syntax oldBoundaryId (since := "2026-10-22")
  | `(old_boundary_id% $e %) => `($e)

-- Field notation requires adjacency, as recorded by `checkNoWsBefore` in its formatter.
/-- info: example (n : Nat) : Nat := n.succ -/
#guard_msgs (drop warning, all) in
#apply_suggestions! example (n : Nat) : Nat := old_boundary_id% n %.succ

end

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

/-! ## Operands of `binop%`, `unop%` and `binrel%` -/

-- These elaborators expand the macros in their operands themselves.
/--
warning: syntax 'oldAdd' has been deprecated: use `+` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵a̵d̵d̵ ̵1̵ ̵2̵(̲1̲ ̲+̲ ̲2̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (1 + 2) * 3 : Nat
---
info: #check (1 + 2) * 3
-/
#guard_msgs in
#apply_suggestions #check old_add 1 2 * 3

/--
warning: syntax 'oldNeg' has been deprecated: use `-` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵n̵e̵g̵ ̵(̵1̵(̲-̲(̲1̲ : I̵n̵t̵)̵I̲n̲t̲)̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: - -1 : Int
---
info: #check -(-(1 : Int))
-/
#guard_msgs in
#apply_suggestions #check -old_neg (1 : Int)

/--
warning: syntax 'oldSucc' has been deprecated: use `Nat.succ` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵s̵u̵c̵c̵ ̵1̵(̲N̲a̲t̲.̲s̲u̲c̲c̲ ̲1̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: Nat.succ 1 = 2 : Prop
---
info: #check (Nat.succ 1) = 2
-/
#guard_msgs in
#apply_suggestions #check old_succ 1 = 2

syntax:50 (name := oldLe) term:51 " ≤' " term:51 : term
macro_rules | `($a ≤' $b) => `($a ≤ $b)

deprecated_syntax oldLe "use `≤` instead" (since := "2026-10-19")
  | `($a ≤' $b) => `($a ≤ $b)

-- Deprecated syntax nested in deprecated syntax is reported as well.
/--
warning: syntax 'oldLe' has been deprecated: use `≤` instead

Hint: Replace the deprecated syntax:
  1 +' 2 ≤'̵ 3

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'oldPlus' has been deprecated: use `+` instead

Hint: Replace the deprecated syntax:
  1 +'̵ 2

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (1 + 2 ≤ 3) = True : Prop
-/
#guard_msgs in
#check (1 +' 2 ≤' 3) = True

macro "wrapped_add" : term => `(old_add 1 2)

/--
warning: macro 'termWrapped_add' (expanded from '«term_+_»') produces deprecated syntax 'oldAdd': use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: 1 + 2 + 3 : Nat
-/
#guard_msgs in
#check wrapped_add + 3

-- Deprecated syntax is not reported in deprecated declarations.
#guard_msgs in
@[deprecated "use `+` instead" (since := "2026-10-19")]
def deprecatedAdd : Nat := old_add 1 2 * 3

/-! ## `do` elements -/

syntax (name := oldReturn) "old_return " term : doElem
macro_rules | `(doElem| old_return $e) => `(doElem| return $e)

deprecated_syntax oldReturn "use `return` instead" (since := "2026-10-19")
  | `(doElem| old_return $e) => `(doElem| return $e)

/--
warning: syntax 'oldReturn' has been deprecated: use `return` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵return 1

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: def doReturnTest : Id Nat := do
  return 1
-/
#guard_msgs in
#apply_suggestions def doReturnTest : Id Nat := do
  old_return 1

-- `unless` is implemented by an elaborator rather than a macro.
deprecated_syntax Lean.Parser.Term.doUnless "use `match` instead" (since := "2026-10-19")
  | `(doElem| unless $c do $s) => `(doElem| match $c:term with | true => pure () | false => $s)

/--
warning: syntax 'Lean.Parser.Term.doUnless' has been deprecated: use `match` instead

Hint: Replace the deprecated syntax:
  u̵n̵l̵e̵s̵s̵ ̵b̵ ̵d̵o̵
  ̵ ̵ ̵ ̵ ̵r̵e̵t̵u̵r̵n̵ ̵1̵m̲a̲t̲c̲h̲ ̲b̲ ̲w̲i̲t̲h̲
  ̲ ̲ ̲|̲ ̲t̲r̲u̲e̲ ̲=̲>̲
  ̲ ̲ ̲ ̲ ̲p̲u̲r̲e̲ ̲(̲)̲
  ̲ ̲ ̲|̲ ̲f̲a̲l̲s̲e̲ ̲=̲>̲
  ̲ ̲ ̲ ̲ ̲r̲e̲t̲u̲r̲n̲ ̲1̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: def doUnlessTest (b : Bool) : Id Nat := do
  match b with
  | true =>
    pure ()
  | false =>
    return 1
  return 2
-/
#guard_msgs in
#apply_suggestions def doUnlessTest (b : Bool) : Id Nat := do
  unless b do
    return 1
  return 2

-- Nested actions are lifted out of the syntax before it is elaborated, so there is no suggestion.
/--
warning: syntax 'Lean.Parser.Term.doUnless' has been deprecated: use `match` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def doUnlessNestedTest (b : Id Bool) : Id Nat := do
  unless (← b) do
    return 1
  return 2

deprecated_syntax Lean.Parser.Term.doUnless "use `match` instead" (since := "2026-10-19")

/-! ## Patterns -/

/--
warning: syntax 'oldSucc' has been deprecated: use `Nat.succ` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵s̵u̵c̵c̵ ̵n̵(̲N̲a̲t̲.̲s̲u̲c̲c̲ ̲n̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: def patternTest : Nat → Nat
  | (Nat.succ n) => n
  | _ => 0
-/
#guard_msgs in
#apply_suggestions def patternTest : Nat → Nat
  | old_succ n => n
  | _ => 0

/--
warning: syntax 'oldZero' has been deprecated: use `Nat.zero` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵N̲a̲t̲.̲zero

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: def doMatchTest (n : Nat) : Id Nat := do
  match n with
  | Nat.zero => return 1
  | _ => return 0
-/
#guard_msgs in
#apply_suggestions def doMatchTest (n : Nat) : Id Nat := do
  match n with
  | old_zero => return 1
  | _ => return 0

macro "zero_pat" : term => `(old_zero)

/--
warning: macro 'termZero_pat' produces deprecated syntax 'oldZero': use `Nat.zero` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def macroPatternTest : Nat → Nat
  | zero_pat => 1
  | _ => 0

-- Elaboration of the `match` is postponed until the type of `n` is known.
/--
warning: syntax 'oldSucc' has been deprecated: use `Nat.succ` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵s̵u̵c̵c̵ ̵k̵(̲N̲a̲t̲.̲s̲u̲c̲c̲ ̲k̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat → Nat := (fun n => match n with | old_succ k => k | _ => 0 : _ → Nat)

/-! ## Syntax definitions -/

syntax:arg (name := oldMany) stx:max "*'" : stx
macro_rules | `(stx| $p*') => `(stx| $p*)

deprecated_syntax oldMany "use `*` instead" (since := "2026-10-19")
  | `(stx| $p*') => `(stx| $p*)

/--
warning: syntax 'oldMany' has been deprecated: use `*` instead

Hint: Replace the deprecated syntax:
  num*'̵

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: syntax "nums " num* : term
-/
#guard_msgs in
#apply_suggestions syntax "nums " num*' : term

/--
warning: syntax 'oldMany' has been deprecated: use `*` instead

Hint: Replace the deprecated syntax:
  num*'̵

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: macro "nums' " num* : term => `(0)
-/
#guard_msgs in
#apply_suggestions macro "nums' " num*' : term => `(0)

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

/-! ## Parenthesization of tactics -/

syntax:lead (name := oldChoice) "old_choice" : tactic
macro_rules | `(tactic| old_choice) => `(tactic| first | skip | fail "no")

deprecated_syntax oldChoice (since := "2026-10-22")
  | _ => `(tactic| first | skip | fail "no")

-- The left precedences agree, but the right end of `first` would absorb the following `<;>`.
/--
info: example : True := by
  (first
    | skip
    | fail "no") <;> exact True.intro
-/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : True := by
  old_choice <;> exact True.intro

syntax (name := oldTry) "old_try" : tactic
macro_rules | `(tactic| old_try) => `(tactic| try fail "no")

deprecated_syntax oldTry (since := "2026-10-22")
  | _ => `(tactic| try fail "no")

/--
info: example : True := by
  (try fail "no") <;> exact True.intro
-/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : True := by
  old_try <;> exact True.intro

syntax (name := oldRepeat) "old_repeat" : tactic
macro_rules | `(tactic| old_repeat) => `(tactic| repeat fail "no")

deprecated_syntax oldRepeat (since := "2026-10-22")
  | _ => `(tactic| repeat fail "no")

/--
info: example : True := by
  (repeat fail "no") <;> exact True.intro
-/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : True := by
  old_repeat <;> exact True.intro

syntax (name := oldAndThen) "old_and_then" : tactic
macro_rules | `(tactic| old_and_then) => `(tactic| skip <;> skip)

deprecated_syntax oldAndThen (since := "2026-10-22")
  | _ => `(tactic| skip <;> skip)

-- A replacement used on the right of `<;>` must also remain a single tactic.
/--
info: example : True := by
  skip <;> (skip <;> skip)
  trivial
-/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : True := by
  skip <;> old_and_then
  trivial

syntax:1 (name := oldSeq) tactic " <;>' " tactic:2 : tactic
macro_rules | `(tactic| $a:tactic <;>' $b:tactic) => `(tactic| $a:tactic <;> $b:tactic)

deprecated_syntax oldSeq (since := "2026-10-22")
  | `(tactic| $a:tactic <;>' $b:tactic) => `(tactic| $a:tactic <;> $b:tactic)

-- Equal precedences do not require parentheses.
/--
info: example : True ∧ True := by
  constructor <;> trivial
-/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : True ∧ True := by
  constructor <;>' trivial

deprecated_syntax oldChoice (since := "2026-10-22")
  | _ => `(tactic| (first | skip | fail "no"))

-- Parentheses supplied by the replacement are not doubled.
/--
info: example : True := by
  (first
    | skip
    | fail "no") <;> exact True.intro
-/
#guard_msgs (drop warning, all) in
#apply_suggestions! example : True := by
  old_choice <;> exact True.intro

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

-- The alternative reaches the maximum recursion depth.
syntax (name := oldLoop) "old_loop" : term
macro_rules | `(old_loop) => `(42)

partial def loopMacro : Lean.Macro := fun stx => Lean.Macro.withIncRecDepth stx (loopMacro stx)

deprecated_syntax oldLoop "use `42` instead" (since := "2026-10-20")
  | stx => loopMacro stx

/--
warning: syntax 'oldLoop' has been deprecated: use `42` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : Nat := old_loop

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

/-! ## Syntax without implementation -/

syntax (name := noImplTac) "no_impl_tac" : tactic

deprecated_syntax noImplTac "use `trivial` instead" (since := "2026-10-20")
  | `(tactic| no_impl_tac) => `(tactic| trivial)

/--
warning: syntax 'noImplTac' has been deprecated: use `trivial` instead

Hint: Replace the deprecated syntax:
  n̵o̵_̵i̵m̵p̵l̵_̵t̵a̵c̵t̲r̲i̲v̲i̲a̲l̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: Tactic `noImplTac` has not been implemented
---
info: example : True := by trivial
-/
#guard_msgs in
#apply_suggestions example : True := by no_impl_tac

syntax (name := declinedTac) "declined_tac" : tactic
macro_rules | `(tactic| declined_tac) => Lean.Macro.throwUnsupported

deprecated_syntax declinedTac "use `trivial` instead" (since := "2026-10-20")
  | `(tactic| declined_tac) => `(tactic| trivial)

-- Every macro for the tactic declines it.
/--
warning: syntax 'declinedTac' has been deprecated: use `trivial` instead

Hint: Replace the deprecated syntax:
  d̵e̵c̵l̵i̵n̵e̵d̵_̵t̵a̵c̵t̲r̲i̲v̲i̲a̲l̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: Unexpected syntax
  declined_tac
---
info: example : True := by trivial
-/
#guard_msgs in
#apply_suggestions example : True := by declined_tac

syntax (name := noImplConv) "no_impl_conv" : conv

deprecated_syntax noImplConv "use `rfl` instead" (since := "2026-10-20")
  | `(conv| no_impl_conv) => `(conv| rfl)

/--
warning: syntax 'noImplConv' has been deprecated: use `rfl` instead

Hint: Replace the deprecated syntax:
  n̵o̵_̵i̵m̵p̵l̵_̵c̵o̵n̵v̵r̲f̲l̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: Tactic `noImplConv` has not been implemented
---
info: example (a : Nat) : a = a := by conv => rfl
-/
#guard_msgs in
#apply_suggestions example (a : Nat) : a = a := by conv => no_impl_conv

syntax (name := noImplTerm) "no_impl_term" : term

deprecated_syntax noImplTerm "use `0` instead" (since := "2026-10-20")
  | `(no_impl_term) => `(0)

/--
warning: syntax 'noImplTerm' has been deprecated: use `0` instead

Hint: Replace the deprecated syntax:
  n̵o̵_̵i̵m̵p̵l̵_̵t̵e̵r̵m̵0̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: elaboration function for `noImplTerm` has not been implemented
  no_impl_term
---
info: example : Nat := 0
-/
#guard_msgs in
#apply_suggestions example : Nat := no_impl_term

syntax (name := noImplDo) "no_impl_do" : doElem

deprecated_syntax noImplDo "use `pure ()` instead" (since := "2026-10-20")
  | `(doElem| no_impl_do) => `(doElem| pure ())

/--
warning: syntax 'noImplDo' has been deprecated: use `pure ()` instead

Hint: Replace the deprecated syntax:
  n̵o̵_̵i̵m̵p̵l̵_̵d̵o̵p̲u̲r̲e̲ ̲(̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: elaboration function for `noImplDo` has not been implemented
  no_impl_do
---
info: example : IO Unit := do pure ()
-/
#guard_msgs in
#apply_suggestions example : IO Unit := do no_impl_do

syntax (name := noImplCmd) "#no_impl_cmd" : command

deprecated_syntax noImplCmd "use `#check` instead" (since := "2026-10-20")
  | `(#no_impl_cmd) => `(#check 0)

/--
warning: syntax 'noImplCmd' has been deprecated: use `#check` instead

Hint: Replace the deprecated syntax:
  #̵n̵o̵_̵i̵m̵p̵l̵_̵c̵m̵d̵#̲c̲h̲e̲c̲k̲ ̲0̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: elaboration function for `noImplCmd` has not been implemented
---
info: #check 0
-/
#guard_msgs in
#apply_suggestions #no_impl_cmd

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

/-! ## `grind` tactics -/

open Lean Elab in
/-- Adds the kind of the innermost tactic whose info tree contains each suggestion in `tree`. -/
partial def addSuggestionTactics (tactic? : Option SyntaxNodeKind)
    (kinds : Array (Option SyntaxNodeKind)) :
    InfoTree → Array (Option SyntaxNodeKind)
  | .context _ tree => addSuggestionTactics tactic? kinds tree
  | .node info children =>
    let tactic? := if let .ofTacticInfo i := info then some i.stx.getKind else tactic?
    let kinds := match info with
      | .ofCustomInfo { value, .. } =>
        if (value.get? Meta.Tactic.TryThis.TryThisInfo).isSome then kinds.push tactic? else kinds
      | _ => kinds
    children.foldl (addSuggestionTactics tactic?) kinds
  | .hole _ => kinds

open Lean Elab Command in
/--
Elaborates `cmd` and logs, for each code action suggestion, the kind of the innermost tactic whose
info tree contains it.
-/
elab "#suggestion_tactics " cmd:command : command => do
  let initTrees ← modifyGet fun s => (s.infoState.trees, { s with infoState.trees := {} })
  elabCommand cmd
  let trees := (← get).infoState.trees
  modify fun s => { s with infoState.trees := initTrees ++ trees }
  logInfo m!"{trees.foldl (addSuggestionTactics none) #[]}"

-- The suggestion for a deprecated tactic is part of the info tree of the tactic.
/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵exact h

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: [some (oldExact)]
-/
#guard_msgs in
#suggestion_tactics example (h : True) : True := by old_exact h

syntax (name := oldGrindFinish) "old_grind_finish" : grind
macro_rules | `(grind| old_grind_finish) => `(grind| finish)
macro_rules | `(grind| old_grind_finish) => `(grind| fail "not this one")

deprecated_syntax oldGrindFinish "use `finish` instead" (since := "2026-10-22")
  | `(grind| old_grind_finish) => `(grind| finish)

-- Only the macro that succeeds reports the deprecation.
/--
warning: syntax 'oldGrindFinish' has been deprecated: use `finish` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵g̵r̵i̵n̵d̵_̵finish

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => finish
-/
#guard_msgs in
#apply_suggestions! example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => old_grind_finish

/--
warning: syntax 'oldGrindFinish' has been deprecated: use `finish` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵g̵r̵i̵n̵d̵_̵finish

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: [some (oldGrindFinish)]
-/
#guard_msgs in
#suggestion_tactics example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => old_grind_finish

syntax (name := noImplGrind) "no_impl_grind" : grind

deprecated_syntax noImplGrind "use `finish` instead" (since := "2026-10-22")
  | `(grind| no_impl_grind) => `(grind| finish)

/--
warning: syntax 'noImplGrind' has been deprecated: use `finish` instead

Hint: Replace the deprecated syntax:
  n̵o̵_̵i̵m̵p̵l̵_̵g̵r̵i̵n̵d̵f̲i̲n̲i̲s̲h̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: Grind tactic `noImplGrind` has not been implemented
---
info: example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => finish
-/
#guard_msgs in
#apply_suggestions example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => no_impl_grind

/--
warning: syntax 'noImplGrind' has been deprecated: use `finish` instead

Hint: Replace the deprecated syntax:
  n̵o̵_̵i̵m̵p̵l̵_̵g̵r̵i̵n̵d̵f̲i̲n̲i̲s̲h̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
error: Grind tactic `noImplGrind` has not been implemented
---
info: [some (noImplGrind)]
-/
#guard_msgs in
#suggestion_tactics example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => no_impl_grind

/-! ## Macro-generated deprecated syntax -/

macro "wrapper" : tactic => `(tactic| old_exact trivial)

-- The fix belongs in the macro, so there is no suggestion.
/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : True := by wrapper

/-! ## Quotations -/

-- Deprecated syntax in quotations that are checked for unbound identifiers is reported in the macro.
/--
warning: quotation uses deprecated syntax 'oldAdd': use `+` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵a̵d̵d̵ ̵1̵ ̵2̵(̲1̲ ̲+̲ ̲2̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: macro "quoted_add" : term => ``((1 + 2))
-/
#guard_msgs in
#apply_suggestions macro "quoted_add" : term => ``(old_add 1 2)

-- Antiquotations are passed to the replacement.
/--
warning: quotation uses deprecated syntax 'oldAdd': use `+` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵a̵d̵d̵ ̵$̵x̵ ̵2̵(̲$̲x̲ ̲+̲ ̲2̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: macro "quoted_add_antiquot " x:term:max : term => ``(($x + 2))
-/
#guard_msgs in
#apply_suggestions macro "quoted_add_antiquot " x:term:max : term => ``(old_add $x 2)

/--
warning: quotation uses deprecated syntax 'oldAdd': use `+` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵a̵d̵d̵ ̵1̵ ̵2̵(̲1̲ ̲+̲ ̲2̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: notation "notation_add" => (1 + 2)
-/
#guard_msgs in
#apply_suggestions notation "notation_add" => old_add 1 2

-- Notation variables are rewritten into antiquotations, so there is no suggestion.
/--
warning: quotation uses deprecated syntax 'oldAdd': use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions notation "notation_add_var " x:max => old_add x 2

/--
warning: quotation uses deprecated syntax 'oldPlus': use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions notation "notation_plus_var " x:max => x +' 2

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

/-! ## `_` patterns -/

syntax (name := oldTrivial) "old_trivial" : tactic
macro_rules | `(tactic| old_trivial) => `(tactic| trivial)

deprecated_syntax oldTrivial "use `trivial` instead" (since := "2026-10-20")
  | _ => `(tactic| trivial)

/--
warning: syntax 'oldTrivial' has been deprecated: use `trivial` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵trivial

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example : True := by trivial
-/
#guard_msgs in
#apply_suggestions example : True := by old_trivial

syntax (name := oldIgnore) "old_ignore " term:max : term
macro_rules | `(old_ignore $_) => `(0)

deprecated_syntax oldIgnore "use `0` instead" (since := "2026-10-20")
  | _ => `(0)

-- The alternative receives every use of the syntax, whatever its arguments.
/--
warning: syntax 'oldIgnore' has been deprecated: use `0` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵i̵g̵n̵o̵r̵e̵ ̵5̵0̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example : Nat := 0
-/
#guard_msgs in
#apply_suggestions example : Nat := old_ignore 5

syntax (name := oldDeclined) "old_declined" : term
macro_rules | `(old_declined) => `(0)

deprecated_syntax oldDeclined "use `0` instead" (since := "2026-10-20")
  | _ => Lean.Macro.throwUnsupported

-- The alternative declines the syntax.
/--
warning: syntax 'oldDeclined' has been deprecated: use `0` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : Nat := old_declined

/-! ## Core syntax -/

-- The replacement is declared in `Init.Tactics`.
/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Hint: Replace the deprecated syntax:
  r̵w̵a̵(̲r̲w̲ [h] at * ̲<̲;̲>̲ ̲a̲s̲s̲u̲m̲p̲t̲i̲o̲n̲)̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (a b : Nat) (h : a = b) (h' : a = 0) : b = 0 := by
  (rw [h] at * <;> assumption)
-/
#guard_msgs in
#apply_suggestions! example (a b : Nat) (h : a = b) (h' : a = 0) : b = 0 := by
  rwa [h] at *

/-! ## Syntax from other sources -/

-- Syntax that a metaprogram parses from a string has positions in that string rather than in the
-- file, so there is no suggestion.
/--
warning: syntax 'oldNum' has been deprecated: use `42` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions run_cmd do
  let stx ← Lean.ofExcept <| Lean.Parser.runParserCategory (← Lean.getEnv) `term "old_num"
  discard <| Lean.Elab.Command.liftTermElabM <| Lean.Elab.Term.elabTerm stx none

-- The positions may be outside the file.
/--
warning: syntax 'oldNum' has been deprecated: use `42` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
run_cmd do
  let stx ← Lean.ofExcept <| Lean.Parser.runParserCategory (← Lean.getEnv) `term
    ("".pushn ' ' 1000000 ++ "old_num")
  discard <| Lean.Elab.Command.liftTermElabM <| Lean.Elab.Term.elabTerm stx none

/-! ## Redeprecation without alternatives removes the replacement -/

deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-19")

/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example (h : True) : True := by old_exact h

/-! ## Invalid alternatives -/

-- A `deprecated_syntax` command with invalid alternatives has no effect, so this deprecation and
-- its replacement stay in place.
deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $e)

/--
error: invalid deprecated_syntax alternative, unexpected syntax node kind `Lean.Parser.Tactic.exact`
-/
#guard_msgs in
deprecated_syntax oldExact (since := "2026-10-19")
  | `(tactic| exact $e) => `(tactic| exact $e)

/--
error: invalid deprecated_syntax alternative, expected a syntax quotation pattern or a single identifier or `_` pattern
-/
#guard_msgs in
deprecated_syntax oldExact (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $e)
  | _ => `(tactic| trivial)

-- An alternative that fails to elaborate.
/--
error: failed to synthesize instance of type class
  HAdd (Lean.TSyntax `term) Nat (Lean.TSyntax `term)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
deprecated_syntax oldExact (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $(e + 1))

-- An alternative that uses `sorry`.
/--
error: invalid deprecated_syntax alternatives, they must not use `sorry`
---
warning: declaration uses `sorry`
-/
#guard_msgs in
deprecated_syntax oldExact (since := "2026-10-19")
  | `(tactic| old_exact $_) => sorry

/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵exact h

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: example (h : True) : True := by exact h
-/
#guard_msgs in
#apply_suggestions example (h : True) : True := by old_exact h

-- Section variables used by alternatives would become parameters of the replacement.
section
variable (n : Nat)

/--
error: invalid deprecated_syntax alternatives, they must not refer to section variables
-/
#guard_msgs in
deprecated_syntax oldNum (since := "2026-10-20")
  | `(old_num) => `($(Lean.quote n))

end

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

-- A replacement registered by other means is ignored if it is not a `Macro`.
def notAMacro (n : Nat) : Lean.Macro := fun _ => `($(Lean.quote n))

run_cmd Lean.modifyEnv (Lean.Elab.deprecatedSyntaxReplacementExt.addEntry · (`oldNum, some ``notAMacro))

/--
warning: syntax 'oldNum' has been deprecated: use `42` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
#apply_suggestions example : Nat := old_num
