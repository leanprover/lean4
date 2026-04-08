/-!
# Testing the `pp.deepTerms false` option

Implemented in PR #3201.
-/

set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8

/-!
Subterms of terms with depth <= pp.deepTerms.threshold are not omitted
-/
#check Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ

/-!
Shallow subterms (subterms with depth <= pp.deepTerms.threshold/4) of terms with
depth > pp.deepTerms.threshold are not omitted
-/
#check Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ

/-!
Deep subterms of terms with depth > pp.deepTerms.threshold are omitted
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

/-!
Checking the message when an omission is copied from the Infoview
-/
#check [1, 2, 3, 4, 5, 6, 7, 8, ⋯]
