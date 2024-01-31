/-!
# Testing the `pp.omitDeepTerms true` option

Implemented in PR #3201.
-/

set_option pp.omitDeepTerms true
set_option pp.omitDeepTerms.threshold 8

/-!
Subterms of terms with depth <= pp.omitDeepTerms.threshold are not omitted
-/
#check Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ

/-!
Shallow subterms (subterms with depth <= pp.omitDeepTerms.threshold/4) of terms with
depth > pp.omitDeepTerms.threshold are not omitted
-/
#check Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ

/-!
Deep subterms of terms with depth > pp.omitDeepTerms.threshold are omitted
-/
#check Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ

/-!
Nothing is omitted in short lists
-/
#check [1, 2, 3, 4, 5, 6, 7, 8]

/-!
In longer lists, the tail is omitted
-/
#check [1, 2, 3, 4, 5, 6, 7, 8, 9]
