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

def noArguments : Nat := noArguments

def noNonFixedArguments (n : Nat) : Nat := noNonFixedArguments n

def Array.sum (xs : Array Nat) : Nat := xs.foldl (init := 0) Nat.add

namespace InterestingMatrix
def f : (n m l : Nat) → Nat
  | n+1, m+1, l+1 => #[
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by decreasing_tactic
end InterestingMatrix

namespace InterestingMatrixWithForbiddenArguments
def f : (n m : Nat) → (h : True) → Nat → Nat
  | n+1, m+1, h, l+1 => #[
      f (n+1) (m+1) h (l+1),
      f (n+1) (m-1) h (l),
      f (n)   (m+1) h (l) ].sum
  | _, _, _, _ => 0
decreasing_by decreasing_tactic
end InterestingMatrixWithForbiddenArguments

namespace InterestingMatrixWithNames
-- Hopefully eventually lean will pick up names even with pattern match syntax
def f (n m l : Nat) : Nat := match n, m, l with
  | n+1, m+1, l+1 => #[
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by decreasing_tactic
end InterestingMatrixWithNames

namespace Mutual
mutual
  def f (fixed n m l : Nat) : Nat := match n, m, l with
    | n+1, m+1, l+1 => #[
        f fixed (n+1) (m+1) (l+1),
        f fixed (n+1) (m-1) (l),
        g fixed (n)   (m+1) trivial (l)].sum
    | _, _, _ => 0

  def g (fixed n m : Nat) (H : True) (l : Nat) : Nat := match n, m, l with
    | n+1, m+1, l+1 => #[
        g fixed (m+1) (n+1) H (l+1),
        g fixed (m+1) (n-1) H (l),
        h fixed (m)   (n+1)  ].sum
    | _, _, _ => 0

  def h (fixed : Nat) : (n m : Nat) -> Nat
    | n+1, m+1 => #[
        f fixed (n+1) (m+1) (n+1),
        h fixed (n+1) (m-1),
        h fixed (n)   (m+1) ].sum
    | _, _ => 0
end
end Mutual


namespace DuplicatedCall

def dup (a : Nat) (b : Nat := a) := a + b

def f : (n m : Nat) → Nat
  | 0, m => m
  | n+1, m => dup (f (n+2) (m+1))

end DuplicatedCall

namespace TrickyCode

-- These tests run GuessLex on peculiar code that it once stumbled over, or might
-- stumble over in the future.

-- The GuessLex code at some point did not like eta-contracted motives in `casesOn`.
def FinPlus1 n := Fin (n + 1)
def badCasesOn (n m : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := FinPlus1) n (⟨0,Nat.zero_lt_succ _⟩) (fun n => Fin.succ (badCasesOn n (.succ m)))
-- termination_by badCasesOn n m => n
decreasing_by decreasing_tactic


-- This actually also fails with an explicit termination_by, and could be fixed
-- by eta-expanding the motive.
-- TODO: Fix by using eta-expanding variant of lambdaTelescope, e.g.
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Going.20under.20exactly.20one.20lambda/near/404278529
def badCasesOn2 (n m : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := FinPlus1) n (⟨0,Nat.zero_lt_succ _⟩) (fun n => Fin.succ (badCasesOn2 n (.succ m)))
termination_by badCasesOn2 n m => n
decreasing_by decreasing_tactic

-- The GuessLex code at does not like `casesOn` alternative with insufficient lambdas
-- TODO: Fix by using eta-expanding variant of lambdaTelescope, e.g.
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Going.20under.20exactly.20one.20lambda/near/404278529
def Fin_succ_comp (f : (n : Nat) → Fin (n + 1)) : (n : Nat) → Fin (n + 2) := fun n => Fin.succ (f n)
def badCasesOn3 (n m : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := fun n => Fin (n + 1)) n (⟨0,Nat.zero_lt_succ _⟩)
      (Fin_succ_comp (fun n => badCasesOn3 n (.succ m)))
-- termination_by badCasesOn3 n m => n
decreasing_by decreasing_tactic


-- Same test, explicit termination_by
def badCasesOn4 (n m : Nat) : Fin (n + 1) :=
   Nat.casesOn (motive := fun n => Fin (n + 1)) n (⟨0,Nat.zero_lt_succ _⟩)
      (Fin_succ_comp (fun n => badCasesOn4 n (.succ m)))
termination_by badCasesOn4 n m => n
decreasing_by decreasing_tactic

end TrickyCode
