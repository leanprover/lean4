/-!
Tests the code actions of `deprecated_syntax` replacement suggestions. Their info must be part of the
info tree of the deprecated command or tactic, which must still be reported for hovers and
incremental tactic elaboration.
-/

set_option linter.deprecated.syntax true

syntax (name := oldCheck) "#old_check " term : command
macro_rules | `(#old_check $e) => `(#check $e)

deprecated_syntax oldCheck "use `#check` instead" (since := "2026-10-19")
  | `(#old_check $e) => `(#check $e)

#old_check Nat
 --^ codeAction
           --^ textDocument/hover

syntax (name := oldExact) "old_exact " term : tactic
macro_rules | `(tactic| old_exact $e) => `(tactic| exact $e)

deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $e)

example (h : True) : True := by old_exact h
                                --^ codeAction

syntax (name := noImplTac) "no_impl_tac" : tactic

deprecated_syntax noImplTac "use `trivial` instead" (since := "2026-10-20")
  | `(tactic| no_impl_tac) => `(tactic| trivial)

example : True := by no_impl_tac
                     --^ codeAction
                     --^ textDocument/hover

syntax (name := oldNum) "old_num" : term
macro_rules | `(old_num) => `(42)

deprecated_syntax oldNum "use `42` instead" (since := "2026-10-19")
  | `(old_num) => `(42)

example : Nat := old_num
                 --^ codeAction

example : Nat := old_num * 2
                 --^ codeAction

example : old_num = 42 := rfl
          --^ codeAction

macro "quoted_num" : term => ``(old_num)
                                --^ codeAction
                                --^ textDocument/hover

notation "notation_num" => old_num
                           --^ codeAction

syntax (name := oldReturn) "old_return " term : doElem
macro_rules | `(doElem| old_return $e) => `(doElem| return $e)

deprecated_syntax oldReturn "use `return` instead" (since := "2026-10-19")
  | `(doElem| old_return $e) => `(doElem| return $e)

def doReturnTest : Id Nat := do
  old_return 1
  --^ codeAction

deprecated_syntax Lean.Parser.Term.doUnless "use `match` instead" (since := "2026-10-19")
  | `(doElem| unless $c do $s) => `(doElem| match $c:term with | true => pure () | false => $s)

def doUnlessTest (b : Bool) : Id Nat := do
  unless b do return 1
  --^ codeAction
  return 2

def patternTest : Nat → Nat
  | old_num => 1
    --^ codeAction
  | _ => 0

syntax:arg (name := oldMany) stx:max "*'" : stx
macro_rules | `(stx| $p*') => `(stx| $p*)

deprecated_syntax oldMany "use `*` instead" (since := "2026-10-19")
  | `(stx| $p*') => `(stx| $p*)

syntax "nums " num*' : term
                --^ codeAction

macro "nums' " num*' : term => `(0)
                --^ codeAction

syntax (name := oldGrindFinish) "old_grind_finish" : grind
macro_rules | `(grind| old_grind_finish) => `(grind| finish)

deprecated_syntax oldGrindFinish "use `finish` instead" (since := "2026-10-22")
  | `(grind| old_grind_finish) => `(grind| finish)

example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => old_grind_finish
           --^ codeAction

syntax (name := noImplGrind) "no_impl_grind" : grind

deprecated_syntax noImplGrind "use `finish` instead" (since := "2026-10-22")
  | `(grind| no_impl_grind) => `(grind| finish)

example (op : Nat → Nat → Nat) [Std.Associative op] (a b c d : Nat) :
    d = op b c → op a d = op (op a b) c := by
  grind => no_impl_grind
           --^ codeAction
