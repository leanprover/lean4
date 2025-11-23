import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check miscellaneous namespaces: -/

#guard_msgs in
#grind_lint check (min := 20) in Acc Attr Bool Clause Const Decidable DefaultClause DHashMap Equiv ExceptT ExtDHashMap Fin Int Internal InvImage Lex LRAT Nat NormalizePattern OldCollector Option OptionT Perm Prod PSigma Quot Quotient Rat Raw ReaderT ReflCmp Setoid StateT Subrelation Subtype Sum Tactic Task Vector WellFounded
