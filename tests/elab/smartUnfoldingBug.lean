import Lean.Elab
open Nat

structure ProvedSkip(n m: Nat) where
  result : Nat
  lt : m < n → result = m
  ge : n ≤ m → result = m + 1

def provedSkip (n m : Nat) : ProvedSkip n m :=
  if c : m < n then
    ⟨m, fun _ => rfl, fun hyp => False.elim (Nat.lt_irrefl m (Nat.lt_of_lt_of_le c hyp))⟩
  else
    ⟨m + 1, fun hyp => absurd hyp c, fun _ => rfl⟩

def skip: Nat → Nat → Nat :=
  fun n m => (provedSkip n m).result

theorem skip_below_eq(n m : Nat) : m < n → (skip n m = m) :=
  fun hyp => (provedSkip n m).lt hyp

theorem skip_above_eq(n m : Nat) : n ≤ m → (skip n m = m + 1) :=
  fun hyp => (provedSkip n m).ge hyp

theorem skip_not_below_eq(n m : Nat) : Not (m < n) → (skip n m = m + 1) :=
  fun hyp =>
    let lem : n ≤ m :=
      match Nat.lt_or_ge m n with
      | Or.inl lt => absurd lt hyp
      | Or.inr ge => ge
    skip_above_eq n m lem

theorem skip_lt: (k j: Nat) →  skip k j < j + 2 :=
    fun k j =>
      if c : j < k then
        let eqn := skip_below_eq k j c
        by
          rw [eqn]
          apply Nat.le_step
          apply Nat.le_refl
          done
      else
        let eqn := skip_not_below_eq k j c
        by
          rw [eqn]
          apply Nat.le_refl
          done

theorem skip_le_succ {n k j : Nat} : j < n → skip k j < n + 1 :=
   by
    intro hyp
    apply Nat.le_trans (skip_lt k j)
    apply Nat.succ_lt_succ
    exact hyp

def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

theorem witness_independent{α : Type}{n : Nat}(seq: FinSeq n α) :
    (i : Nat)→ (j : Nat) → (iw : i < n) → (jw : j < n) →
        (i = j) → seq i iw = seq j jw :=
        fun i j iw jw eqn =>
          match j, eqn, jw with
          | .(i), rfl, ijw =>
               rfl

namespace FinSeq
def init {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α :=
  fun k w =>
      seq k (Nat.le_step w)

def last{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq n (Nat.le_refl _)

def delete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α): FinSeq n α :=
  fun j w =>
    seq (skip k j) (skip_le_succ w)

end FinSeq

inductive Vector' (α : Type) : Nat → Type where
  | nil : Vector' α zero
  | cons{n: Nat}(head: α) (tail: Vector'  α n) : Vector' α  (n + 1)

infixr:66 "+:" => Vector'.cons

open Vector'

def Vector'.coords {α : Type}{n : Nat}(v: Vector' α n) : FinSeq n α :=
  fun j jw =>
  match n, v, j, jw with
  | .(zero), nil, k, lt => nomatch lt
  | m + 1, cons head tail, zero, lt => head
  | m + 1, cons head tail, j + 1, w =>  tail.coords j (Nat.le_of_succ_le_succ w)

def seqVecAux {α: Type}{n m l: Nat}: (s : n + m = l) →
    (seq1 : FinSeq n α) → (accum : Vector' α m) →
       Vector' α l:=
    match n with
    | zero => fun s => fun _ => fun seq2 =>
      by
        have ss : l = m := by
          rw [← s]
          apply Nat.zero_add
          done
        have sf : Vector' α l = Vector' α m := by
          rw [ss]
        exact Eq.mpr sf seq2
        done
    | k + 1 => fun s seq1 seq2 =>
      let ss : k + (m + 1)  = l :=
        by
          rw [← s]
          rw [(Nat.add_comm m 1)]
          rw [(Nat.add_assoc k 1 m)]
          done
      seqVecAux ss (seq1.init) ((seq1.last) +: seq2)

def FinSeq.vec {α : Type}{n: Nat} : FinSeq n α  →  Vector' α n :=
    fun seq => seqVecAux (Nat.add_zero n) seq Vector'.nil

def Clause(n : Nat) : Type := Vector' (Option Bool) n

def Valuation(n: Nat) : Type := Vector' Bool n

inductive SatAnswer{dom n: Nat}(clauses : Vector' (Clause n) dom) where
  | unsat : SatAnswer clauses
  | sat :  SatAnswer clauses

structure SimpleRestrictionClauses{dom n: Nat}
    (clauses: Vector' (Clause (n + 1)) dom) where
  codom : Nat
  restClauses : Vector'  (Clause n) codom

def prependRes{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector' (Clause (n + 1)) dom):
        (rd : SimpleRestrictionClauses clauses) →
           (head : Clause (n + 1)) →
        SimpleRestrictionClauses (head +: clauses) :=
        fun rd  head =>
          if c : head.coords focus focusLt = some branch then
            ⟨rd.codom, rd.restClauses⟩
          else
            ⟨rd.codom + 1, (FinSeq.vec (FinSeq.delete focus focusLt head.coords)) +: rd.restClauses⟩

def restClauses{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
        (clauses: Vector' (Clause (n + 1)) dom) :
         SimpleRestrictionClauses clauses :=
            match dom, clauses with
            | 0, _ =>  ⟨0, Vector'.nil⟩
            | m + 1, Vector'.cons head clauses =>
                prependRes branch focus focusLt clauses
                            (restClauses branch focus focusLt clauses) head

def answerSAT{n dom : Nat}: (clauses : Vector' (Clause n) dom) →  SatAnswer clauses :=
      match n with
      | zero =>
           match dom with
            | zero => fun cls => SatAnswer.sat
            | l + 1 => fun _ =>  SatAnswer.unsat
      | m + 1 =>
        fun clauses =>
        let cls := clauses
        let bd := zero_lt_succ m
        let rd  :=
            restClauses false zero bd clauses
        let subCls := rd.restClauses
        let subSol: SatAnswer subCls := answerSAT subCls
        match subSol with
        | SatAnswer.sat   =>
          SatAnswer.sat
        | SatAnswer.unsat  =>
            let rd := restClauses true zero bd cls -- replacing cls by clauses fixes this
            let subCls := rd.restClauses
            let subSol : SatAnswer subCls := answerSAT subCls
            match subSol with
            | SatAnswer.sat   =>
                SatAnswer.sat
            | SatAnswer.unsat   =>
                SatAnswer.unsat

open Lean.Meta
open Lean.Elab.Term

syntax (name:= nrmlform)"whnf!" term : term
@[term_elab nrmlform] def normalformImpl : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `(whnf! $s) =>
      do
        let t ← elabTerm s none
        let e ← whnf t
        return e
  | _ => Lean.Elab.throwIllFormedSyntax


def cls1 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector'.nil

def cls2 : Clause 2 := (some true) +: none +: Vector'.nil  -- P

def egStatement := cls1 +: cls2 +: Vector'.nil

def egAnswer : SatAnswer egStatement := answerSAT egStatement

def egAnswerNorm : SatAnswer egStatement := whnf! egAnswer
