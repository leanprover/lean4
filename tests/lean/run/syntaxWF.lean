namespace Lean.Syntax

theorem sizeOf_getArg_of_not_missing
    (h : stx ≠ missing)
    : sizeOf (stx.getArg i) < sizeOf stx := by
  cases stx with
  | missing => simp at h
  | atom _ val => cases val; simp_arith [getArg]
  | ident _ _ val _ => cases val <;> simp_arith [getArg]
  | node _ kind args =>
    simp [getArg, Array.getD]
    split
    . apply Nat.lt_trans (Array.sizeOf_get ..)
      simp_arith
    . cases kind <;> simp_arith

theorem sizeOf_getArg_of_isOfKind {stx : Syntax}
    (h₁ : stx.isOfKind k)
    (h₂ : (`missing == k) = false)
    : sizeOf (stx.getArg i) < sizeOf stx := by
  apply sizeOf_getArg_of_not_missing
  intro h; subst h
  simp [isOfKind, getKind, h₂] at h₁

theorem sizeOf_getArg_of_matchesNull {stx : Syntax}
    (h : stx.matchesNull n)
    : sizeOf (stx.getArg i) < sizeOf stx := by
  apply sizeOf_getArg_of_not_missing
  intro he; subst he
  simp [matchesNull, isNodeOf] at h

macro "syntax_dec" : tactic =>
  `(first
     | apply sizeOf_getArg_of_isOfKind; assumption; decide; done
     | apply sizeOf_getArg_of_matchesNull; assumption; decide; done
     | apply Nat.lt_trans (sizeOf_getArg_of_isOfKind ?h1 ?h2)
       case' h1 => try (assumption); done
       case' h2 => try (decide); done
     | apply Nat.lt_trans (sizeOf_getArg_of_matchesNull ?h)
       case' h => assumption)

macro_rules |
  `(tactic| decreasing_trivial) => `(tactic| (repeat syntax_dec); done)

end Lean.Syntax
open Lean.Syntax

open Lean

def visit (stx : Syntax) : Syntax :=
  match stx with
  | `(if $c then $t else $e) => visit c
  | `(let $x:ident := $v:term; if $c then $t else $e) => visit c
  | _ => stx
