namespace Unary

def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by p => p

derive_functional_induction ackermann

/--
info: Unary.ackermann.induct (motive : Nat × Nat → Prop) (case1 : ∀ (m : Nat), motive (0, m))
  (case2 : ∀ (n : Nat), motive (n, 1) → motive (Nat.succ n, 0))
  (case3 : ∀ (n m : Nat), motive (n + 1, m) → motive (n, ackermann (n + 1, m)) → motive (Nat.succ n, Nat.succ m))
  (x : Nat × Nat) : motive x
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
derive_functional_induction ackermann

/--
info: Binary.ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
  (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m)) :
  ∀ (a a_1 : Nat), motive a a_1
-/
#guard_msgs in
#check ackermann.induct

end Binary

universe u
opaque _root_.List.attach : {α : Type u} → (l : List α) → List { x // x ∈ l }

inductive Tree | node : List Tree → Tree
def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.map (fun ⟨t, _ht⟩ => t.rev) |>.reverse)
derive_functional_induction Tree.rev

/--
info: Tree.rev.induct (motive : Tree → Prop)
  (case1 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive t) → motive (Tree.node ts)) (x : Tree) : motive x
-/
#guard_msgs in
#check Tree.rev.induct


def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n+2 => fib n + fib (n+1)
termination_by n => n

derive_functional_induction fib
/--
info: fib.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive n → motive (n + 1) → motive (Nat.succ (Nat.succ n))) (x : Nat) : motive x
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
derive_functional_induction have_tailrec

/--
info: have_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), n < n + 1 → motive n → motive (Nat.succ n)) (x : Nat) : motive x
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
derive_functional_induction have_non_tailrec

/--
info: have_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
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
derive_functional_induction let_tailrec

/--
info: let_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 :
    ∀ (n : Nat),
      let h2 := ⋯;
      motive n → motive (Nat.succ n))
  (x : Nat) : motive x
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
derive_functional_induction let_non_tailrec

/--
info: let_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
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
      with_ite_tailrec n
termination_by n => n
derive_functional_induction with_ite_tailrec

/--
info: with_ite_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), n % 2 = 0 → motive n → motive (Nat.succ n))
  (case3 : ∀ (n : Nat), ¬n % 2 = 0 → motive n → motive (Nat.succ n)) (x : Nat) : motive x
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
derive_functional_induction with_ite_non_tailrec

/--
info: with_ite_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive (n + 1) → motive n → motive (Nat.succ (Nat.succ n))) (x : Nat) : motive x
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
derive_functional_induction with_dite_non_tailrec

/--
info: with_dite_non_tailrec.induct (motive : Nat → Prop)
(case1 : ∀ (x : Nat), (x - 1 < x → motive (x - 1)) → motive x)
  (x : Nat) : motive x
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
derive_functional_induction with_dite_tailrec

/--
info: with_dite_tailrec.induct (motive : Nat → Prop)
(case1 : ∀ (x : Nat), x - 1 < x → motive (x - 1) → motive x)
  (case2 : ∀ (x : Nat), ¬x - 1 < x → motive x) (x : Nat) : motive x
-/
#guard_msgs in
#check with_dite_tailrec.induct

set_option linter.unusedVariables false in
def with_match_refining_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    match n with
    | 0 => with_match_refining_tailrec 0
    | m => with_match_refining_tailrec m
termination_by n => n
derive_functional_induction with_match_refining_tailrec

/--
info: with_match_refining_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 0 → motive (Nat.succ 0))
  (case3 : ∀ (m : Nat), (m = 0 → False) → motive m → motive (Nat.succ m)) (x : Nat) : motive x
-/
#guard_msgs in
#check with_match_refining_tailrec.induct



def with_arg_refining_match1 (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 =>
    if h : i = 0 then 0 else with_arg_refining_match1 (i - 1) n
termination_by i
derive_functional_induction with_arg_refining_match1

/--
info: with_arg_refining_match1.induct (motive : Nat → Nat → Prop) (case1 : ∀ (i : Nat), motive i 0)
  (case2 : ∀ (n : Nat), motive 0 (Nat.succ n))
  (case3 : ∀ (i n : Nat), ¬i = 0 → motive (i - 1) n → motive i (Nat.succ n)) (i : Nat) : ∀ (a : Nat), motive i a
-/
#guard_msgs in
#check with_arg_refining_match1.induct

def with_arg_refining_match2 (i : Nat) (n : Nat) : Nat :=
  if i = 0 then 0 else match n with
  | 0 => 0
  | n+1 => with_arg_refining_match2 (i - 1) n
termination_by i
derive_functional_induction with_arg_refining_match2

/--
info: with_arg_refining_match2.induct (motive : Nat → Nat → Prop) (case1 : ∀ (n : Nat), motive 0 n)
  (case2 : ∀ (i : Nat), ¬i = 0 → motive i 0)
  (case3 : ∀ (i : Nat), ¬i = 0 → ∀ (n : Nat), motive (i - 1) n → motive i (Nat.succ n)) (i n : Nat) : motive i n
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
derive_functional_induction with_other_match_tailrec

/--
info: with_other_match_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), n % 2 = 0 → motive n → motive (Nat.succ n))
  (case3 : ∀ (n : Nat), (n % 2 = 0 → False) → motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check with_other_match_tailrec.induct

set_option linter.unusedVariables false in
def with_mixed_match_tailrec : Nat → Nat → Nat → Nat → Nat := fun a b c d =>
  match a, h: b, c % 2, h : d % 2 with
  | 0, _, _, _ => 0
  | a+1, x, y, z => with_mixed_match_tailrec a x y z
termination_by n => n
derive_functional_induction with_mixed_match_tailrec

/--
info: with_mixed_match_tailrec.induct (motive : Nat → Nat → Nat → Nat → Prop) (case1 : ∀ (a a_1 x : Nat), motive 0 x a a_1)
  (case2 : ∀ (a a_1 a_2 x : Nat), motive a_2 x (a % 2) (a_1 % 2) → motive (Nat.succ a_2) x a a_1) :
  ∀ (a a_1 a_2 a_3 : Nat), motive a a_1 a_2 a_3
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
derive_functional_induction with_mixed_match_tailrec2

/--
info: with_mixed_match_tailrec2.induct (motive : Nat → Nat → Nat → Nat → Nat → Prop)
  (case1 : ∀ (a a_1 a_2 a_3 : Nat), motive 0 a a_1 a_2 a_3) (case2 : ∀ (a a_1 n x : Nat), motive (Nat.succ n) 0 x a a_1)
  (case3 : ∀ (a a_1 n a_2 x : Nat), motive n a_2 x (a % 2) (a_1 % 2) → motive (Nat.succ n) (Nat.succ a_2) x a a_1) :
  ∀ (a a_1 a_2 a_3 a_4 : Nat), motive a a_1 a_2 a_3 a_4
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
derive_functional_induction with_match_non_tailrec

/--
info: with_match_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n)) (x : Nat) : motive x
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
derive_functional_induction with_match_non_tailrec_refining

/--
info: with_match_non_tailrec_refining.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 :
    ∀ (n : Nat),
      (match n with
        | 0 => motive 0
        | m => motive m) →
        motive (Nat.succ n))
  (x : Nat) : motive x
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
derive_functional_induction with_overlap

/--
info: with_overlap.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1) (case3 : motive 2) (case4 : motive 3)
  (case5 : ∀ (n : Nat), (n = 0 → False) → (n = 1 → False) → (n = 2 → False) → motive n → motive (Nat.succ n))
  (x : Nat) : motive x
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
derive_functional_induction unary

/--
info: UnusedExtraParams.unary.induct (base : Nat) (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check unary.induct

def binary (base : Nat) : Nat → Nat → Nat
  | 0, m => base + m
  | n+1, m => binary base n m
termination_by n => n
derive_functional_induction binary

/--
info: UnusedExtraParams.binary.induct (base : Nat) (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n m : Nat), motive n m → motive (Nat.succ n) m) : ∀ (a a_1 : Nat), motive a a_1
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

derive_functional_induction match_non_tail

/--
info: NonTailrecMatch.match_non_tail.induct (motive : Nat → Prop)
  (case1 :
    ∀ (x : Nat),
      (match x with
        | 0 => True
        | 1 => True
        | Nat.succ (Nat.succ n) => motive n ∧ motive (n + 1)) →
        motive x)
  (x : Nat) : motive x
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
derive_functional_induction foo

/--
info: AsPattern.foo.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
-/
#guard_msgs in
#check foo.induct



def bar (n : Nat) :=
  1 +
  match n with
  | 0 => 0
  | x@(n+1) => x + bar n
termination_by n
derive_functional_induction bar

/--
info: AsPattern.bar.induct (motive : Nat → Prop)
  (case1 :
    ∀ (x : Nat),
      (match x with
        | 0 => True
        | x@h:(Nat.succ n) => motive n) →
        motive x)
  (x : Nat) : motive x
-/
#guard_msgs in
#check bar.induct

end AsPattern

namespace GramSchmidt

-- this tried to repoduce a problem with gramSchmidt,
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
decreasing_by
  simp_wf
  simp [below_lt, *]

derive_functional_induction foo
/--
info: GramSchmidt.foo.induct (motive : Nat → Prop) (case1 : ∀ (x : Nat), (∀ (i : Nat), below x i → motive i) → motive x)
  (x : Nat) : motive x
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
derive_functional_induction foo
/--
info: LetFun.foo.induct.{u_1} {α : Type u_1} (x : α) (motive : List α → Prop) (case1 : motive [])
  (case2 : ∀ (_y : α) (ys : List α), motive ys → motive (_y :: ys)) : ∀ (x : List α), motive x
-/
#guard_msgs in
#check foo.induct


def bar {α} (x : α) : List α → Nat
  | .nil => 0
  | .cons _y ys =>
      have this := bar x ys
      this
termination_by xs => xs

derive_functional_induction bar
/--
info: LetFun.bar.induct.{u_1} {α : Type u_1} (x : α) (motive : List α → Prop) (case1 : motive [])
  (case2 : ∀ (_y : α) (ys : List α), motive ys → motive (_y :: ys)) : ∀ (x : List α), motive x
-/
#guard_msgs in
#check bar.induct

end LetFun


namespace RecCallInDisrs

def foo : Nat → Nat
  | 0 => 0
  | n+1 => if foo n = 0 then 1 else 0
termination_by n => n
derive_functional_induction foo

/--
info: RecCallInDisrs.foo.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), foo n = 0 → motive n → motive (Nat.succ n))
  (case3 : ∀ (n : Nat), ¬foo n = 0 → motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check foo.induct


def bar : Nat → Nat
  | 0 => 0
  | n+1 => match h₁ : n, bar n with
    | 0, 0 => 0
    | 0, _ => 1
    | m+1, _ => bar m
termination_by n => n
derive_functional_induction bar

/--
info: RecCallInDisrs.bar.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : bar 0 = 0 → motive 0 → motive (Nat.succ 0))
  (case3 : (bar 0 = 0 → False) → motive 0 → motive (Nat.succ 0))
  (case4 : ∀ (m : Nat), motive (Nat.succ m) → motive m → motive (Nat.succ (Nat.succ m))) (x : Nat) : motive x
-/
#guard_msgs in
#check bar.induct

end RecCallInDisrs

namespace EvenOdd

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
derive_functional_induction even

/--
info: EvenOdd.even.induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0) (case2 : motive2 0)
  (case3 : ∀ (n : Nat), motive2 n → motive1 (Nat.succ n)) (case4 : ∀ (n : Nat), motive1 n → motive2 (Nat.succ n)) :
  ∀ (a : Nat), motive1 a
-/
#guard_msgs in
#check even.induct

/--
info: EvenOdd.odd.induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0) (case2 : motive2 0)
  (case3 : ∀ (n : Nat), motive2 n → motive1 (Nat.succ n)) (case4 : ∀ (n : Nat), motive1 n → motive2 (Nat.succ n)) :
  ∀ (a : Nat), motive2 a
-/
#guard_msgs in
#check odd.induct

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
derive_functional_induction Tree.map

/--
info: Tree.Tree.map.induct (f : Tree → Tree) (motive1 : Tree → Prop) (motive2 : List Tree → Prop)
  (case1 : ∀ (ts : List Tree), motive2 ts → motive1 (Tree.node ts))
  (case2 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive1 t) → motive2 ts) : ∀ (a : Tree), motive1 a
-/
#guard_msgs in
#check Tree.map.induct

/--
info: Tree.Tree.map_forest.induct (f : Tree → Tree) (motive1 : Tree → Prop) (motive2 : List Tree → Prop)
  (case1 : ∀ (ts : List Tree), motive2 ts → motive1 (Tree.node ts))
  (case2 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive1 t) → motive2 ts) (ts : List Tree) : motive2 ts
-/
#guard_msgs in
#check Tree.map_forest.induct

end Tree

namespace DefaultArgument

-- Default arguments should not be copied over

def unary (fixed : Bool := false) (n : Nat := 0)  : Nat :=
  match n with
  | 0 => 0
  | n+1 => unary fixed n
termination_by n
derive_functional_induction unary

/--
info: DefaultArgument.unary.induct (fixed : Bool) (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check unary.induct

def foo (fixed : Bool := false) (n : Nat) (m : Nat := 0) : Nat :=
  match n with
  | 0 => m
  | n+1 => foo fixed n m
termination_by n
derive_functional_induction foo

/--
info: DefaultArgument.foo.induct (fixed : Bool) (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (m n : Nat), motive n m → motive (Nat.succ n) m) (n m : Nat) : motive n m
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
derive_functional_induction foo

/--
info: Nary.foo.induct (motive : Nat → Nat → (k : Nat) → Fin k → Prop)
  (case1 : ∀ (x x_1 : Nat) (x_2 : Fin x_1), motive 0 x x_1 x_2)
  (case2 : ∀ (x x_1 : Nat) (x_2 : Fin x_1), (x = 0 → False) → motive x 0 x_1 x_2)
  (case3 : ∀ (x x_1 : Nat) (x_2 : Fin 0), (x = 0 → False) → (x_1 = 0 → False) → motive x x_1 0 x_2)
  (case4 : ∀ (x x_1 : Nat) (x_2 : Fin 1), (x = 0 → False) → (x_1 = 0 → False) → motive x x_1 1 x_2)
  (case5 :
    ∀ (n m k : Nat) (x : Fin (k + 2)),
      motive n m (k + 1) ⟨0, ⋯⟩ → motive (Nat.succ n) (Nat.succ m) (Nat.succ (Nat.succ k)) x) :
  ∀ (a a_1 k : Nat) (a_2 : Fin k), motive a a_1 k a_2
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
derive_functional_induction foo

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
  (x : Nat) : motive x
-/
#guard_msgs in
#check foo.induct

end Dite

namespace CommandIdempotence

-- This checks that the `derive_functional_induction` command gracefully handles being called twice

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

derive_functional_induction even._mutual

/--
info: CommandIdempotence.even._mutual.induct (motive : Nat ⊕' Nat → Prop) (case1 : motive (PSum.inl 0))
  (case2 : motive (PSum.inr 0)) (case3 : ∀ (n : Nat), motive (PSum.inr n) → motive (PSum.inl (Nat.succ n)))
  (case4 : ∀ (n : Nat), motive (PSum.inl n) → motive (PSum.inr (Nat.succ n))) (x : Nat ⊕' Nat) : motive x
-/
#guard_msgs in
#check even._mutual.induct

/-- error: unknown constant 'CommandIdempotence.even.induct' -/
#guard_msgs in
#check even.induct

derive_functional_induction even

/--
info: CommandIdempotence.even._mutual.induct (motive : Nat ⊕' Nat → Prop) (case1 : motive (PSum.inl 0))
  (case2 : motive (PSum.inr 0)) (case3 : ∀ (n : Nat), motive (PSum.inr n) → motive (PSum.inl (Nat.succ n)))
  (case4 : ∀ (n : Nat), motive (PSum.inl n) → motive (PSum.inr (Nat.succ n))) (x : Nat ⊕' Nat) : motive x
-/
#guard_msgs in
#check even._mutual.induct

/--
info: CommandIdempotence.even.induct (motive1 motive2 : Nat → Prop) (case1 : motive1 0) (case2 : motive2 0)
  (case3 : ∀ (n : Nat), motive2 n → motive1 (Nat.succ n)) (case4 : ∀ (n : Nat), motive1 n → motive2 (Nat.succ n)) :
  ∀ (a : Nat), motive1 a
-/
#guard_msgs in
#check even.induct

derive_functional_induction even

end CommandIdempotence

namespace Errors

/-- error: unknown constant 'doesNotExist' -/
#guard_msgs in
derive_functional_induction doesNotExist

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  foo 0 #[]
where
  foo (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩
      if p a then
        foo (i+1) (r.push a)
      else
        r
    else
      r
  termination_by as.size - i

/--
error: Function Errors.takeWhile does not look like a function defined by well-founded recursion.
NB: If Errors.takeWhile is not itself recursive, but contains an inner recursive function (via `let rec` or `where`), try `Errors.takeWhile.go` where `go` is name of the inner function.
-/
#guard_msgs in
derive_functional_induction takeWhile -- Cryptic error message

derive_functional_induction takeWhile.foo

end Errors

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
derive_functional_induction foo

/--
info: PreserveParams.foo.induct (a : Nat) (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), a = 23 → motive (Nat.succ n)) (case3 : ¬a = 23 → motive (Nat.succ a))
  (case4 : ∀ (n : Nat), ¬a = 23 → ¬a = n → motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check foo.induct


end PreserveParams
