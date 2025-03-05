import Lean.Elab.Command
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Meta.Tactic.FunInd

set_option guard_msgs.diff true

namespace Unary

def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by p => p

/--
info: Unary.ackermann.induct (motive : Nat × Nat → Prop) (case1 : ∀ (m : Nat), motive (0, m))
  (case2 : ∀ (n : Nat), motive (n, 1) → motive (n.succ, 0))
  (case3 : ∀ (n m : Nat), motive (n + 1, m) → motive (n, ackermann (n + 1, m)) → motive (n.succ, m.succ))
  (a✝ : Nat × Nat) : motive a✝
-/
#guard_msgs in
#check ackermann.induct

end Unary

namespace Binary

def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n, m)

/--
info: Binary.ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n : Nat), motive n 1 → motive n.succ 0)
  (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive n.succ m.succ) (a✝ a✝¹ : Nat) :
  motive a✝ a✝¹
-/
#guard_msgs in
#check ackermann.induct

end Binary

universe u

inductive Tree | node : List Tree → Tree
def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.map (fun ⟨t, _ht⟩ => t.rev) |>.reverse)

/--
info: Tree.rev.induct (motive : Tree → Prop)
  (case1 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive t) → motive (Tree.node ts)) (a✝ : Tree) : motive a✝
-/
#guard_msgs in
#check Tree.rev.induct


def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n+2 => fib n + fib (n+1)
termination_by n => n

/--
info: fib.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive n → motive (n + 1) → motive n.succ.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check fib.induct

set_option linter.unusedVariables false in
def have_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    have h2 : n < n+1 := Nat.lt_succ_self n
    have_tailrec n
termination_by n => n

/--
info: have_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), n < n + 1 → motive n → motive n.succ)
  (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check have_tailrec.induct

set_option linter.unusedVariables false in
def have_non_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    Nat.succ <|
      have h2 : n < n+1 := Nat.lt_succ_self n
      have_non_tailrec n
termination_by n => n

/--
info: have_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check have_non_tailrec.induct

set_option linter.unusedVariables false in
def let_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    let h2 : n < n+1 := Nat.lt_succ_self n
    let_tailrec n
termination_by n => n

/--
info: let_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ) (a✝ : Nat) :
  motive a✝
-/
#guard_msgs in
#check let_tailrec.induct

set_option linter.unusedVariables false in
def let_non_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    Nat.succ <|
      let h2 : n < n+1 := Nat.lt_succ_self n
      let_non_tailrec n
termination_by n => n

/--
info: let_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check let_non_tailrec.induct


set_option linter.unusedVariables false in
def with_ite_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    if n % 2 = 0 then
      with_ite_tailrec n
    else
      with_ite_tailrec (n-1)
termination_by n => n

/--
info: with_ite_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), n % 2 = 0 → motive n → motive n.succ)
  (case3 : ∀ (n : Nat), ¬n % 2 = 0 → motive (n - 1) → motive n.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check with_ite_tailrec.induct


set_option linter.unusedVariables false in
def with_ite_non_tailrec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 =>
    Nat.succ <|
      if n % 2 = 0 then
        with_ite_non_tailrec (n+1)
      else
        with_ite_non_tailrec n
termination_by n => n

/--
info: with_ite_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive (n + 1) → motive n → motive n.succ.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check with_ite_non_tailrec.induct

set_option linter.unusedVariables false in
def with_dite_non_tailrec (n : Nat) : Nat :=
  Nat.succ <|
    if h : n - 1 < n then
      with_dite_non_tailrec (n-1)
    else
      0
termination_by n

/--
info: with_dite_non_tailrec.induct (motive : Nat → Prop) (case1 : ∀ (x : Nat), (x - 1 < x → motive (x - 1)) → motive x)
  (n : Nat) : motive n
-/
#guard_msgs in
#check with_dite_non_tailrec.induct

set_option linter.unusedVariables false in
def with_dite_tailrec (n : Nat) : Nat :=
    if h : n - 1 < n then
      with_dite_tailrec (n-1)
    else
      0
termination_by n

/--
info: with_dite_tailrec.induct (motive : Nat → Prop) (case1 : ∀ (x : Nat), x - 1 < x → motive (x - 1) → motive x)
  (case2 : ∀ (x : Nat), ¬x - 1 < x → motive x) (n : Nat) : motive n
-/
#guard_msgs in
#check with_dite_tailrec.induct

set_option linter.unusedVariables false in
def with_bif_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    bif n % 2 == 0 then
      with_bif_tailrec n
    else
      with_bif_tailrec (n-1)
termination_by n => n

/--
info: with_bif_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), (n % 2 == 0) = true → motive n → motive n.succ)
  (case3 : ∀ (n : Nat), (n % 2 == 0) = false → motive (n - 1) → motive n.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check with_bif_tailrec.induct

set_option linter.unusedVariables false in
def with_match_refining_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    match n with
    | 0 => with_match_refining_tailrec 0
    | m => with_match_refining_tailrec m
termination_by n => n

/--
info: with_match_refining_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 0 → motive (Nat.succ 0))
  (case3 : ∀ (m : Nat), (m = 0 → False) → motive m → motive m.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check with_match_refining_tailrec.induct



def with_arg_refining_match1 (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 =>
    if h : i = 0 then 0 else with_arg_refining_match1 (i - 1) n
termination_by i

/--
info: with_arg_refining_match1.induct (motive : Nat → Nat → Prop) (case1 : ∀ (i : Nat), motive i 0)
  (case2 : ∀ (n : Nat), motive 0 n.succ) (case3 : ∀ (i n : Nat), ¬i = 0 → motive (i - 1) n → motive i n.succ)
  (i a✝ : Nat) : motive i a✝
-/
#guard_msgs in
#check with_arg_refining_match1.induct

def with_arg_refining_match2 (i : Nat) (n : Nat) : Nat :=
  if i = 0 then 0 else match n with
  | 0 => 0
  | n+1 => with_arg_refining_match2 (i - 1) n
termination_by i

/--
info: with_arg_refining_match2.induct (motive : Nat → Nat → Prop) (case1 : ∀ (n : Nat), motive 0 n)
  (case2 : ∀ (i : Nat), ¬i = 0 → motive i 0)
  (case3 : ∀ (i : Nat), ¬i = 0 → ∀ (n : Nat), motive (i - 1) n → motive i n.succ) (i n : Nat) : motive i n
-/
#guard_msgs in
#check with_arg_refining_match2.induct


set_option linter.unusedVariables false in
def with_other_match_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    match n % 2 with
    | 0 => with_other_match_tailrec n
    | _ => with_other_match_tailrec n
termination_by n => n

/--
info: with_other_match_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), n % 2 = 0 → motive n → motive n.succ)
  (case3 : ∀ (n : Nat), (n % 2 = 0 → False) → motive n → motive n.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check with_other_match_tailrec.induct

set_option linter.unusedVariables false in
def with_mixed_match_tailrec : Nat → Nat → Nat → Nat → Nat := fun a b c d =>
  match a, h: b, c % 2, h : d % 2 with
  | 0, _, _, _ => 0
  | a+1, x, y, z => with_mixed_match_tailrec a x y z
termination_by n => n

/--
info: with_mixed_match_tailrec.induct (motive : Nat → Nat → Nat → Nat → Prop) (case1 : ∀ (a a_1 x : Nat), motive 0 x a a_1)
  (case2 : ∀ (a a_1 a_2 x : Nat), motive a_2 x (a % 2) (a_1 % 2) → motive a_2.succ x a a_1) (a✝ a✝¹ a✝² a✝³ : Nat) :
  motive a✝ a✝¹ a✝² a✝³
-/
#guard_msgs in
#check with_mixed_match_tailrec.induct

set_option linter.unusedVariables false in
def with_mixed_match_tailrec2 : Nat → Nat → Nat → Nat → Nat → Nat := fun n a b c d =>
  match n with
  | 0 => 0
  | n+1 =>
    match a, h: b, c % 2, h : d % 2 with
    | 0, _, _, _ => 0
    | a+1, x, y, z => with_mixed_match_tailrec2 n a x y z
termination_by n => n

/--
info: with_mixed_match_tailrec2.induct (motive : Nat → Nat → Nat → Nat → Nat → Prop)
  (case1 : ∀ (a a_1 a_2 a_3 : Nat), motive 0 a a_1 a_2 a_3) (case2 : ∀ (a a_1 n x : Nat), motive n.succ 0 x a a_1)
  (case3 : ∀ (a a_1 n a_2 x : Nat), motive n a_2 x (a % 2) (a_1 % 2) → motive n.succ a_2.succ x a a_1)
  (a✝ a✝¹ a✝² a✝³ a✝⁴ : Nat) : motive a✝ a✝¹ a✝² a✝³ a✝⁴
-/
#guard_msgs in
#check with_mixed_match_tailrec2.induct

set_option linter.unusedVariables false in
def with_match_non_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
  Nat.succ <|
    match n % 2 with
    | 0 => with_match_non_tailrec n
    | _ => with_match_non_tailrec n
termination_by n => n

/--
info: with_match_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check with_match_non_tailrec.induct

set_option linter.unusedVariables false in
def with_match_non_tailrec_refining : Nat → Nat
  | 0 => 0
  | n+1 =>
  Nat.succ <|
    match n with
    | 0 => with_match_non_tailrec_refining 0
    | m => with_match_non_tailrec_refining m
termination_by n => n

/--
info: with_match_non_tailrec_refining.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 :
    ∀ (n : Nat),
      (match n with
        | 0 => motive 0
        | m => motive m) →
        motive n.succ)
  (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check with_match_non_tailrec_refining.induct


def with_overlap : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | n+1 => with_overlap n
termination_by n => n

/--
info: with_overlap.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1) (case3 : motive 2) (case4 : motive 3)
  (case5 : ∀ (n : Nat), (n = 0 → False) → (n = 1 → False) → (n = 2 → False) → motive n → motive n.succ) (a✝ : Nat) :
  motive a✝
-/
#guard_msgs in
#check with_overlap.induct

namespace UnusedExtraParams

-- This test how unused fixed function parameters are handled.
-- See comment in the code

def unary (base : Nat) : Nat → Nat
  | 0 => base
  | n+1 => unary base n
termination_by n => n

/--
info: UnusedExtraParams.unary.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check unary.induct

def binary (base : Nat) : Nat → Nat → Nat
  | 0, m => base + m
  | n+1, m => binary base n m
termination_by n => n

/--
info: UnusedExtraParams.binary.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n m : Nat), motive n m → motive n.succ m) (a✝ a✝¹ : Nat) : motive a✝ a✝¹
-/
#guard_msgs in
#check binary.induct

end UnusedExtraParams

namespace NonTailrecMatch

def match_non_tail (n : Nat ) : Bool :=
  n = 42 || match n with
  | 0 => true
  | 1 => true
  | n+2 => match_non_tail n && match_non_tail (n+1)
termination_by n

def match_non_tail_induct
  {motive : Nat → Prop}
  (case1 : forall n, (IH : match n with | 0 => True | n+1 => motive n) → motive n)
  (n : Nat) : motive n :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n IH =>
    match n with
    | 0 => case1 0 True.intro
    | n+1 =>
      case1 (n+1) (IH n (Nat.lt_succ_self _))
  ) n


/--
info: NonTailrecMatch.match_non_tail.induct (motive : Nat → Prop)
  (case1 :
    ∀ (x : Nat),
      (match x with
        | 0 => True
        | 1 => True
        | n.succ.succ => motive n ∧ motive (n + 1)) →
        motive x)
  (n : Nat) : motive n
-/
#guard_msgs in
#check match_non_tail.induct


theorem match_non_tail_eq_true (n : Nat) : match_non_tail n = true := by
  induction n using match_non_tail.induct
  case case1 n IH =>
    unfold match_non_tail
    split <;> dsimp at IH <;> simp [IH]

end NonTailrecMatch


namespace AsPattern

def foo (n : Nat) :=
  match n with
  | 0 => 0
  | x@(n+1) => x + foo n
termination_by n

/--
info: AsPattern.foo.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (n : Nat) : motive n
-/
#guard_msgs in
#check foo.induct



def bar (n : Nat) :=
  1 +
  match n with
  | 0 => 0
  | x@(n+1) => x + bar n
termination_by n

/--
info: AsPattern.bar.induct (motive : Nat → Prop)
  (case1 :
    ∀ (x : Nat),
      (match x with
        | 0 => True
        | x@h:n.succ => motive n) →
        motive x)
  (n : Nat) : motive n
-/
#guard_msgs in
#check bar.induct

end AsPattern

namespace GramSchmidt

-- this tried to reproduce a problem with gramSchmidt,
-- with more proofs from `simp` abstracting over the IH.
-- I couldn't quite reproduce it, but let's keep it.

def below (n i : Nat) := i < n

@[simp]
def below_lt (n i : Nat) (h : below n i) : i < n := h

def sum_below (n : Nat) (f : (i : Nat) → below n i → Nat) :=
  match n with
  | 0 => 0
  | n+1 => sum_below n (fun i hi => f i (Nat.lt_succ_of_le (Nat.le_of_lt hi))) +
          f n (Nat.lt_succ_self n)

def foo (n : Nat) :=
  1 + sum_below n (fun i _ => foo i)
termination_by n
decreasing_by simp [below_lt, *]

/--
info: GramSchmidt.foo.induct (motive : Nat → Prop) (case1 : ∀ (x : Nat), (∀ (i : Nat), below x i → motive i) → motive x)
  (n : Nat) : motive n
-/
#guard_msgs in
#check foo.induct

end GramSchmidt

namespace LetFun

def foo {α} (x : α) : List α → Nat
  | .nil => 0
  | .cons _y ys =>
      let this := foo x ys
      this
termination_by xs => xs
/--
info: LetFun.foo.induct.{u_1} {α : Type u_1} (x : α) (motive : List α → Prop) (case1 : motive [])
  (case2 : ∀ (_y : α) (ys : List α), motive ys → motive (_y :: ys)) (a✝ : List α) : motive a✝
-/
#guard_msgs in
#check foo.induct


def bar {α} (x : α) : List α → Nat
  | .nil => 0
  | .cons _y ys =>
      have this := bar x ys
      this
termination_by xs => xs

/--
info: LetFun.bar.induct.{u_1} {α : Type u_1} (x : α) (motive : List α → Prop) (case1 : motive [])
  (case2 : ∀ (_y : α) (ys : List α), Nat → motive ys → motive (_y :: ys)) (a✝ : List α) : motive a✝
-/
#guard_msgs in
#check bar.induct

end LetFun


namespace RecCallInDisrs

def foo : Nat → Nat
  | 0 => 0
  | n+1 => if foo n = 0 then 1 else 0
termination_by n => n

/--
info: RecCallInDisrs.foo.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), foo n = 0 → motive n → motive n.succ)
  (case3 : ∀ (n : Nat), ¬foo n = 0 → motive n → motive n.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check foo.induct


set_option linter.unusedVariables false in
def bar : Nat → Nat
  | 0 => 0
  | n+1 => match _h : n, bar n with
    | 0, 0 => 0
    | 0, _ => 1
    | m+1, _ => bar m
termination_by n => n

/--
info: RecCallInDisrs.bar.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : bar 0 = 0 → motive 0 → motive (Nat.succ 0))
  (case3 : (bar 0 = 0 → False) → motive 0 → motive (Nat.succ 0))
  (case4 : ∀ (m : Nat), motive m.succ → motive m → motive m.succ.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check bar.induct

end RecCallInDisrs

namespace EvenOdd

mutual
def even : (m : Nat) → Bool -- NB: Does this parameter name appear in the inductions?
  | 0 => true
  | n+1 => odd n
termination_by n => n
def odd : Nat → Bool
  | 0 => false
  | n+1 => even n
termination_by n => n
end

/--
info: EvenOdd.even.induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0) (case2 : ∀ (n : Nat), motive2 n → motive1 n.succ)
  (case3 : motive2 0) (case4 : ∀ (n : Nat), motive1 n → motive2 n.succ) (m : Nat) : motive1 m
-/
#guard_msgs in
#check even.induct

/--
info: EvenOdd.odd.induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0) (case2 : ∀ (n : Nat), motive2 n → motive1 n.succ)
  (case3 : motive2 0) (case4 : ∀ (n : Nat), motive1 n → motive2 n.succ) (a✝ : Nat) : motive2 a✝
-/
#guard_msgs in
#check odd.induct

/--
info: EvenOdd.even.mutual_induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0)
  (case2 : ∀ (n : Nat), motive2 n → motive1 n.succ) (case3 : motive2 0)
  (case4 : ∀ (n : Nat), motive1 n → motive2 n.succ) : (∀ (m : Nat), motive1 m) ∧ ∀ (a : Nat), motive2 a
-/
#guard_msgs in
#check even.mutual_induct

end EvenOdd

namespace Tree

inductive Tree : Type
  | node : List Tree → Tree

mutual
def Tree.map (f : Tree → Tree) : Tree → Tree
  | Tree.node ts => Tree.node (map_forest f ts)

def Tree.map_forest (f : Tree → Tree) (ts : List Tree) : List Tree :=
  ts.attach.map (fun ⟨t, _ht⟩ => Tree.map f t)
end

/--
info: Tree.Tree.map.induct (motive1 : Tree → Prop) (motive2 : List Tree → Prop)
  (case1 : ∀ (ts : List Tree), motive2 ts → motive1 (Tree.node ts))
  (case2 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive1 t) → motive2 ts) (a✝ : Tree) : motive1 a✝
-/
#guard_msgs in
#check Tree.map.induct

/--
info: Tree.Tree.map_forest.induct (motive1 : Tree → Prop) (motive2 : List Tree → Prop)
  (case1 : ∀ (ts : List Tree), motive2 ts → motive1 (Tree.node ts))
  (case2 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive1 t) → motive2 ts) (ts : List Tree) : motive2 ts
-/
#guard_msgs in
#check Tree.map_forest.induct

/--
info: Tree.Tree.map.mutual_induct (motive1 : Tree → Prop) (motive2 : List Tree → Prop)
  (case1 : ∀ (ts : List Tree), motive2 ts → motive1 (Tree.node ts))
  (case2 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive1 t) → motive2 ts) :
  (∀ (a : Tree), motive1 a) ∧ ∀ (ts : List Tree), motive2 ts
-/
#guard_msgs in
#check Tree.map.mutual_induct

end Tree

namespace DefaultArgument

-- Default arguments should not be copied over

def unary (fixed : Bool := false) (n : Nat := 0)  : Nat :=
  match n with
  | 0 => 0
  | n+1 => unary fixed n
termination_by n

/--
info: DefaultArgument.unary.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (n : Nat) : motive n
-/
#guard_msgs in
#check unary.induct

def foo (fixed : Bool := false) (n : Nat) (m : Nat := 0) : Nat :=
  match n with
  | 0 => m
  | n+1 => foo fixed n m
termination_by n

/--
info: DefaultArgument.foo.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive n.succ)
  (n : Nat) : motive n
-/
#guard_msgs in
#check foo.induct

end DefaultArgument

namespace Nary

def foo : Nat → Nat → (k : Nat) → Fin k → Nat
  | 0, _, _, _ => 0
  | _, 0, _, _ => 0
  | _, _, 0, _ => 0
  | _, _, 1, _ => 0
  | n+1, m+1, k+2, _ => foo n m (k+1) ⟨0, Nat.zero_lt_succ _⟩
termination_by n => n

/--
info: Nary.foo.induct (motive : Nat → Nat → (k : Nat) → Fin k → Prop) (case1 : ∀ (k x : Nat) (x_1 : Fin k), motive 0 x k x_1)
  (case2 : ∀ (k x : Nat), (x = 0 → False) → ∀ (x_2 : Fin k), motive x 0 k x_2)
  (case3 : ∀ (x x_1 : Nat), (x = 0 → False) → (x_1 = 0 → False) → ∀ (a : Fin 0), motive x x_1 0 a)
  (case4 : ∀ (x x_1 : Nat), (x = 0 → False) → (x_1 = 0 → False) → ∀ (a : Fin 1), motive x x_1 1 a)
  (case5 : ∀ (n m k : Nat) (a : Fin k.succ.succ), motive n m (k + 1) ⟨0, ⋯⟩ → motive n.succ m.succ k.succ.succ a)
  (a✝ a✝¹ k : Nat) (a✝² : Fin k) : motive a✝ a✝¹ k a✝²
-/
#guard_msgs in
#check foo.induct

end Nary

namespace Dite

def foo (n : Nat) : Nat :=
  let j := n - 1
  if _h : j < n then
    foo j
  else
    42

/--
info: Dite.foo.induct (motive : Nat → Prop)
  (case1 :
    ∀ (x : Nat),
      let j := x - 1;
      j < x → motive j → motive x)
  (case2 :
    ∀ (x : Nat),
      let j := x - 1;
      ¬j < x → motive x)
  (n : Nat) : motive n
-/
#guard_msgs in
#check Dite.foo.induct

end Dite


namespace PreserveParams

/-
Tests that cleaning up the goal state does not throw away useful equalties
relating varying parameters to fixed ones.
-/

def foo (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 =>
    if a = 23 then 23 else
    if a = n then 42 else
    foo a n
termination_by n => n

/--
info: PreserveParams.foo.induct (a : Nat) (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), a = 23 → motive n.succ) (case3 : ¬a = 23 → motive a.succ)
  (case4 : ∀ (n : Nat), ¬a = 23 → ¬a = n → motive n → motive n.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check foo.induct


end PreserveParams

namespace Mutual_Induct

/-! Tests that `mutual_induct` is properly reserved. -/

mutual
def even : Nat → Bool
  | 0 => true
  | n+1 => odd n
termination_by n => n
def odd : Nat → Bool
  | 0 => false
  | n+1 => even n
termination_by n => n
end

-- The following tests uses that guard_msgs reverts the environment,
-- so they all test that the mutual induct is really generated by these commands

/--
info: Mutual_Induct.even.mutual_induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0)
  (case2 : ∀ (n : Nat), motive2 n → motive1 n.succ) (case3 : motive2 0)
  (case4 : ∀ (n : Nat), motive1 n → motive2 n.succ) : (∀ (a : Nat), motive1 a) ∧ ∀ (a : Nat), motive2 a
-/
#guard_msgs in
#check even.mutual_induct

-- The .mutual_induct only exists on the first declaration:

/-- error: unknown constant 'Mutual_Induct.odd.mutual_induct' -/
#guard_msgs in
#check odd.mutual_induct

/-- info: false -/
#guard_msgs in
open Lean Lean.Elab in
run_meta
  logInfo m!"{Lean.Tactic.FunInd.isFunInductName (← getEnv) `Mutual_Induct.odd.mutual_induct}"

def nonmutual : Nat → Bool
  | 0 => true
  | n+1 => nonmutual n

/-- error: unknown constant 'Mutual_Induct.nonmutual.mutual_induct' -/
#guard_msgs in
#check nonmutual.mutual_induct

/--
error: invalid field notation, type is not of the form (C ...) where C is a constant
  id
has type
  ?_ → ?_
-/
#guard_msgs in
set_option pp.mvars false in
#check id.mutual_induct

end Mutual_Induct
