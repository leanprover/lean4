/-!
A few cases where guessing the lexicographic order fails, and
where we want to keep tabs on the output.

All functions take more than one changing argument, because the guesslex
code skips non-mutuals unary functions with only one plausible measure.
-/

def nonTerminating : Nat → Nat → Nat
  | 0, _ => 0
  | n, m => nonTerminating (.succ n) (.succ m)

-- Saying decreasing_by forces Lean to use structural recursion, which gives a different
-- error message
def nonTerminating2 : Nat → Nat → Nat
  | 0, _ => 0
  | n, m => nonTerminating2 (.succ n) (.succ m)
decreasing_by decreasing_tactic


-- The GuessLex code does not like eta-contracted motives in `casesOn`.
-- At the time of writing, the error message is swallowed
-- When guessing the lexicographic order becomes more verbose this will improve.
def FinPlus1 n := Fin (n + 1)
def badCasesOn (n m : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := FinPlus1) n (⟨0,Nat.zero_lt_succ _⟩) (fun n => Fin.succ (badCasesOn n (.succ m)))
decreasing_by decreasing_tactic
-- termination_by badCasesOn n => n


-- Like above, but now with a `casesOn` alternative with insufficient lambdas
def Fin_succ_comp (f : (n : Nat) → Fin (n + 1)) : (n m : Nat) → Fin (n + 2) := fun n => Fin.succ (f n)
def badCasesOn2 (n m : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := fun n => Fin (n + 1)) n (⟨0,Nat.zero_lt_succ _⟩)
      (Fin_succ_comp (fun n => badCasesOn2 n (.succ m)))
decreasing_by decreasing_tactic
-- termination_by badCasesOn2 n => n
