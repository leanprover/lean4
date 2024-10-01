-- This module defines
namespace Nat

-- `forallRange i n f` is true if f holds for all indices j from i to n-1.
def forallRange (i:Nat) (n:Nat) (f: ∀ (j:Nat), j < n → Bool) : Bool :=
  if h:i < n then
    f i h && forallRange (i+1) n f
  else
    true
  termination_by forallRange i n f => n-i

-- `forallRange` correctness theorem.
theorem forallRangeImplies'
  (n i j : Nat)
  (f  : ∀(k:Nat), k < n → Bool)
  (eq : i+j = n)
  (p  : forallRange i n f = true)
  (k  : Nat)
  (lb : i ≤ k)
  (ub : k < n)
  : f k ub = true := by
  induction j generalizing i with
  | zero =>
    simp at eq
    simp [eq] at lb
    have pr := Nat.not_le_of_gt ub
    contradiction
  | succ j ind =>
    have i_lt_n : i < n := Nat.le_trans (Nat.succ_le_succ lb) ub
    unfold forallRange at p
    simp [i_lt_n] at p
    cases Nat.eq_or_lt_of_le lb with
    | inl hEq =>
      subst hEq
      apply p.1
    | inr hLt =>
      have succ_i_add_j : succ i + j = n := by simp_arith [← eq]
      apply ind (succ i) succ_i_add_j p.2 hLt

-- Correctness theorem for `forallRange`
theorem forallRangeImplies (p:forallRange i n f = true) {j:Nat} (lb:i ≤ j) (ub : j < n)
  : f j ub = true :=
    have h : i+(n-i)=n := Nat.add_sub_of_le (Nat.le_trans lb (Nat.le_of_lt ub))
    forallRangeImplies' n i (n-i) f h p j lb ub

theorem lt_or_eq_of_succ {i j:Nat} (lt : i < Nat.succ j) : i < j ∨ i = j :=
  match lt with
  | Nat.le.step m => Or.inl m
  | Nat.le.refl => Or.inr rfl

-- Introduce strong induction principal for natural numbers.
theorem strong_induction_on {p : Nat → Prop} (n:Nat)
  (h:∀n, (∀ m, m < n → p m) → p n) : p n := by
    suffices ∀n m, m < n → p m from this (succ n) n (Nat.lt_succ_self _)
    intros n
    induction n with
    | zero =>
      intros m h
      contradiction
    | succ i ind =>
      intros m h1
      cases Nat.lt_or_eq_of_succ h1 with
      | inl is_lt =>
        apply ind _ is_lt
      | inr is_eq =>
        apply h
        rw [is_eq]
        apply ind

end Nat

-- Introduce strong induction principal for Fin.
theorem Fin.strong_induction_on {P : Fin w → Prop} (i:Fin w)
  (ind : ∀(i:Fin w), (∀(j:Fin w), j < i → P j) → P i)
 : P i := by
   cases i with
   | mk i i_lt =>
     revert i_lt
     apply @Nat.strong_induction_on (λi => ∀ (i_lt : i < w), P { val := i, isLt := i_lt })
     intros j p j_lt_w
     apply ind ⟨j, j_lt_w⟩
     intros z z_lt_j
     apply p _ z_lt_j

namespace PEG

inductive Expression (t : Type) (nt : Type) where
  | epsilon : Expression t nt
  | fail : Expression t nt
  | any : Expression t nt
  | terminal : t → Expression t nt
  | seq : (a b : nt) → Expression t nt
  | choice : (a b : nt) → Expression t nt
  | look : (a : nt) → Expression t nt
  | notP : (e : nt) → Expression t nt

def Grammar (t nt : Type _) := nt → Expression t nt

structure ProofRecord  (nt : Type) where
  leftnonterminal : nt
  success : Bool
  position : Nat
  lengthofspan : Nat
  subproof1index : Nat
  subproof2index : Nat

namespace ProofRecord

def endposition {nt:Type} (r:ProofRecord nt) : Nat := r.position + r.lengthofspan

inductive Result where
  | fail : Result
  | success : Nat → Result

def record_result (r:ProofRecord nt) : Result :=
  if r.success then
    Result.success r.lengthofspan
  else
    Result.fail

end ProofRecord

def PreProof (nt : Type) := Array (ProofRecord nt)

def record_match [dnt : DecidableEq nt] (r:ProofRecord nt) (n:nt) (i:Nat) : Bool :=
  r.leftnonterminal = n && r.position = i

open Expression

section well_formed

variable {t nt : Type}
variable [dt : DecidableEq t]
variable [dnt : DecidableEq nt]
variable (g : Grammar t nt)
variable (s : Array t)

def well_formed_record (p : PreProof nt) (i:Nat) (i_lt : i < p.size) (r : ProofRecord nt) : Bool :=
  let n := r.leftnonterminal
  match g n with
  | epsilon => r.success ∧ r.lengthofspan = 0
  | fail => ¬ r.success
  | any =>
    if r.position < s.size then
      r.success && r.lengthofspan = 1
    else
      ¬ r.success
  | terminal t =>
    if r.position < s.size && s.getD r.position t = t then
      r.success && r.lengthofspan = 1
    else
      ¬ r.success
  | seq a b =>
    r.subproof1index < i &&
      let r1 := p.getD r.subproof1index r
      record_match r1 a r.position &&
        if r1.success then
          r.subproof2index < i &&
            let r2 := p.getD r.subproof2index r
            record_match r2 b r1.endposition &&
              if r2.success then
                r.success && r.endposition = r2.endposition
              else
                ¬r.success
        else
          ¬r.success
  | choice a b =>
    r.subproof1index < i &&
      let r1 := p.getD r.subproof1index r
      record_match r1 a r.position &&
        if r1.success then
          r.success && r.lengthofspan = r1.lengthofspan
        else
          r.subproof2index < i &&
            let r2 := p.getD r.subproof2index r
            record_match r2 b r.position &&
              if r2.success then
                r.success && r.lengthofspan = r2.lengthofspan
              else
                ¬r.success
  | look a =>
    r.subproof1index < i &&
      let r1 := p.getD r.subproof1index r
      record_match r1 a r.position &&
        if r1.success then
          r.success && r.lengthofspan = 0
        else
          ¬r.success
  | notP a =>
    r.subproof1index < i &&
      let r1 := p.getD r.subproof1index r
      record_match r1 a r.position &&
        if r1.success then
          ¬r.success
        else
          r.success && r.lengthofspan = 0


def well_formed_proof (p : PreProof nt) : Bool :=
  Nat.forallRange 0 p.size (λi lt => well_formed_record g s p i lt (p.get ⟨i, lt⟩))

end well_formed

def Proof [DecidableEq t] [DecidableEq nt] (g:Grammar t nt) (s: Array t) :=
  { p:PreProof nt // well_formed_proof g s p }

namespace Proof

variable {g:Grammar t nt}
variable {s : Array t}
variable [DecidableEq t]
variable [DecidableEq nt]

def size (p:Proof g s) := p.val.size

def get (p:Proof g s) : Fin p.size → ProofRecord nt := p.val.get

instance : CoeFun (Proof g s) (fun p => Fin p.size → ProofRecord nt) :=
  ⟨fun p => p.get⟩

theorem has_well_formed_record (p:Proof g s) (i:Fin p.size) :
  well_formed_record g s p.val i.val i.isLt (p i) :=
    Nat.forallRangeImplies p.property (Nat.zero_le i.val) i.isLt

end Proof

section correctness

variable {g:Grammar t nt}
variable {s : Array t}
variable [h1:DecidableEq t]
variable [h2:DecidableEq nt]

-- Lemma to rewrite from dependent use of proof index to get-with-default
theorem proof_get_to_getD (r:ProofRecord nt) (p:Proof g s) (i:Fin p.size)  :
  p i = p.val.getD i.val r := by
  have isLt : i.val < Array.size p.val := i.isLt
  simp [Proof.get, Array.get, Array.getD, isLt ]
  apply congrArg
  apply Fin.eq_of_val_eq
  trivial

set_option tactic.dbg_cache true

theorem is_deterministic
  : forall (p q : Proof g s) (i: Fin p.size) (j: Fin q.size),
      (p i).leftnonterminal = (q j).leftnonterminal
      → (p i).position      = (q j).position
      → (p i).record_result = (q j).record_result := by
  intros p q i0
  induction i0 using Fin.strong_induction_on with
  | ind i ind =>
  intro j eq_nt p_pos_eq_q_pos
  have p_def := p.has_well_formed_record i
  have q_def := q.has_well_formed_record j
  simp only [well_formed_record, eq_nt, p_pos_eq_q_pos] at p_def q_def
  generalize q_j_eq : q j = q_j
  generalize e_eq : g (q_j.leftnonterminal) = e
  simp only [q_j_eq, e_eq] at p_def q_def p_pos_eq_q_pos
  simp only [ProofRecord.record_result]

  cases e
  case epsilon => simp_all
  case fail => simp_all
  case any => simp at q_def; split at q_def <;> simp_all
  case terminal t => simp at q_def; split at q_def <;> simp_all
  case seq a b =>
    simp [record_match, ProofRecord.endposition] at p_def q_def
    generalize p_sub1_eq : (p i).subproof1index = p_sub1
    generalize p_sub2_eq : (p i).subproof2index = p_sub2
    generalize q_sub1_eq : q_j.subproof1index = q_sub1
    generalize q_sub2_eq : q_j.subproof2index = q_sub2
    simp only [p_sub1_eq, p_sub2_eq] at p_def
    simp only [q_sub1_eq, q_sub2_eq] at q_def
    have ⟨p_sub1_bound, ⟨p_sub1_nt, p_sub1_pos⟩, p_def⟩ := p_def
    have ⟨q_sub1_bound, ⟨q_sub1_nt, q_sub1_pos⟩, q_def⟩ := q_def

    have ind1 := ind (Fin.mk p_sub1 (Nat.lt_trans p_sub1_bound i.isLt))
                      p_sub1_bound
                      (Fin.mk q_sub1 (Nat.lt_trans q_sub1_bound j.isLt))
    rw [proof_get_to_getD (p i) p, proof_get_to_getD q_j q] at ind1
    simp [ProofRecord.record_result] at ind1

    split at p_def <;> split at q_def <;> simp [*] at ind1 p_def q_def <;> simp [*]

    have ⟨p_sub2_bound, ⟨p_sub2_nt, p_sub2_pos⟩, p_def⟩ := p_def
    have ⟨q_sub2_bound, ⟨q_sub2_nt, q_sub2_pos⟩, q_def⟩ := q_def

    -- Instantiate second invariant on subterm 2
    have ind2 :=
      ind (Fin.mk p_sub2 (Nat.lt_trans p_sub2_bound i.isLt))
          p_sub2_bound
          (Fin.mk q_sub2 (Nat.lt_trans q_sub2_bound j.isLt))
    rw [proof_get_to_getD (p i) p, proof_get_to_getD q_j q] at ind2

    simp [ProofRecord.record_result] at ind2
    split at p_def <;> split at q_def <;>
      simp_arith [*] at ind2 p_def q_def <;>
      simp_arith [*]
  save
  case choice =>
    simp [record_match] at p_def q_def
    -- checkpoint simp
    generalize p_sub1_eq : (p i).subproof1index = p_sub1
    generalize p_sub2_eq : (p i).subproof2index = p_sub2
    simp only [p_sub1_eq, p_sub2_eq] at p_def

    generalize q_sub1_eq : q_j.subproof1index = q_sub1
    generalize q_sub2_eq : q_j.subproof2index = q_sub2
    simp only [q_sub1_eq, q_sub2_eq] at q_def
    have ⟨p_sub1_bound, ⟨p_sub1_nt, p_sub1_pos⟩, p_def⟩ := p_def
    have ⟨q_sub1_bound, ⟨q_sub1_nt, q_sub1_pos⟩, q_def⟩ := q_def
    have ind1 := ind (Fin.mk p_sub1 (Nat.lt_trans p_sub1_bound i.isLt))
                      p_sub1_bound
                      (Fin.mk q_sub1 (Nat.lt_trans q_sub1_bound j.isLt))

    rw [proof_get_to_getD (p i) p, proof_get_to_getD q_j q] at ind1
    simp [ProofRecord.record_result] at ind1
    save
    trace "type here"
    stop
    split at p_def <;> split at q_def <;> simp_all

    have ⟨p_sub2_bound, ⟨p_sub2_nt, p_sub2_pos⟩, p_def⟩ := p_def
    have ⟨q_sub2_bound, ⟨q_sub2_nt, q_sub2_pos⟩, q_def⟩ := q_def
    -- Instantiate second invariant on subterm 2
    have ind2 :=
      ind (Fin.mk p_sub2 (Nat.lt_trans p_sub2_bound i.isLt))
          p_sub2_bound
          (Fin.mk q_sub2 (Nat.lt_trans q_sub2_bound j.isLt))
    rw [proof_get_to_getD (p i) p, proof_get_to_getD q_j q] at ind2
    simp [ProofRecord.record_result] at ind2
    split at p_def <;> split at q_def <;> simp_all
  stop
  case look =>
    simp [record_match] at p_def q_def

    generalize p_sub1_eq : (p i).subproof1index = p_sub1
    simp only [p_sub1_eq] at p_def

    generalize q_sub1_eq : q_j.subproof1index = q_sub1
    simp only [q_sub1_eq] at q_def
    have ⟨p_sub1_bound, ⟨p_sub1_nt, p_sub1_pos⟩, p_def⟩ := p_def
    have ⟨q_sub1_bound, ⟨q_sub1_nt, q_sub1_pos⟩, q_def⟩ := q_def

    have ind1 := ind (Fin.mk p_sub1 (Nat.lt_trans p_sub1_bound i.isLt))
                      p_sub1_bound
                      (Fin.mk q_sub1 (Nat.lt_trans q_sub1_bound j.isLt))
    rw [proof_get_to_getD (p i) p, proof_get_to_getD q_j q] at ind1
    simp [ProofRecord.record_result] at ind1
    split at p_def <;> split at q_def <;> simp_all
  case notP =>
    simp [record_match] at p_def q_def

    generalize p_sub1_eq : (p i).subproof1index = p_sub1
    simp only [p_sub1_eq] at p_def

    generalize q_sub1_eq : q_j.subproof1index = q_sub1
    simp only [q_sub1_eq] at q_def

    have ⟨p_sub1_bound, ⟨p_sub1_nt, p_sub1_pos⟩, p_def⟩ := p_def
    have ⟨q_sub1_bound, ⟨q_sub1_nt, q_sub1_pos⟩, q_def⟩ := q_def

    have ind1 := ind (Fin.mk p_sub1 (Nat.lt_trans p_sub1_bound i.isLt))
                      p_sub1_bound
                      (Fin.mk q_sub1 (Nat.lt_trans q_sub1_bound j.isLt))
    rw [proof_get_to_getD (p i) p, proof_get_to_getD q_j q] at ind1
    simp [ProofRecord.record_result] at ind1
    split at p_def <;> split at q_def <;> simp_all

end correctness

end PEG
