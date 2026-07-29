import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check miscellaneous namespaces: -/

/--
info: instantiating `Vector.range_succ` triggers 95 additional `grind` theorem instantiations
---
info: Vector.range_succ
[thm] instances
  [thm] Vector.append_assoc ↦ 35
  [thm] Vector.append_assoc_symm ↦ 18
  [thm] Vector.range'_append ↦ 11
  [thm] Vector.range_succ ↦ 6
  [thm] List.size_toArray ↦ 4
  [thm] Vector.append_empty ↦ 4
  [thm] Vector.empty_append ↦ 4
  [thm] Vector.range'_one ↦ 3
  [thm] List.length_cons ↦ 2
  [thm] Vector.range_eq_range' ↦ 2
  [thm] Array.eq_empty_of_size_eq_zero ↦ 1
  [thm] Array.size_empty ↦ 1
  [thm] List.eq_nil_of_length_eq_zero ↦ 1
  [thm] List.length_nil ↦ 1
  [thm] Vector.range'_zero ↦ 1
  [thm] Vector.toArray_empty ↦ 1
---
info: Try this:
  [apply] #grind_lint check  (min := 20) in Acc Attr Bool Clause Const Decidable DefaultClause DHashMap Equiv ExceptT ExtDHashMap
    Fin Int Internal InvImage Lex LRAT Nat NormalizePattern OldCollector Option OptionT Perm Prod PSigma Quot Quotient Rat
    Raw ReaderT ReflCmp Setoid StateT Subrelation Subtype Sum Tactic Task Vector WellFounded
  #grind_lint inspect Vector.range_succ
-/
#guard_msgs in
#grind_lint check (min := 20) in Acc Attr Bool Clause Const Decidable DefaultClause DHashMap Equiv ExceptT ExtDHashMap Fin Int Internal InvImage Lex LRAT Nat NormalizePattern OldCollector Option OptionT Perm Prod PSigma Quot Quotient Rat Raw ReaderT ReflCmp Setoid StateT Subrelation Subtype Sum Tactic Task Vector WellFounded
