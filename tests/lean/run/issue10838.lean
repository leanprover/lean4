set_option warn.sorry false


inductive Ty where
  | unit : Ty
  | arrow (t₁ t₂ : Ty) : Ty

def Env (n : Nat) := Fin n → Ty

def Env.add (Γ : Env n) (t : Ty) : Env (n + 1) :=
  Fin.cases t Γ

inductive Term : Env n → Ty → Type where
  | var (i : Fin n) : Term Γ (Γ i)
  | app (e₁ : Term Γ (.arrow t₁ t₂)) (e₂ : Term Γ t₁) : Term Γ t₂
  | lam (e : Term (Γ.add t₁) t₂) : Term Γ (.arrow t₁ t₂)

def Subst (Γ : Env n) (Δ : Env m) := (i : Fin n) → Term Δ (Γ i)

def Subst.id {Γ : Env n} : Subst Γ Γ :=
  fun i => .var i

def Subst.shift {Γ : Env n} : Subst Γ (Γ.add t) :=
  fun i => .var i.succ

def IsVar : Term Γ t → Bool
  | .var _ => true
  | .app _ _ => false
  | .lam _ => false

attribute [simp] IsVar.eq_1 IsVar.eq_2 IsVar.eq_3

def IsRenaming (σ : Subst Γ Δ) : Bool := ∀ i, IsVar (σ i)

set_option trace.Meta.FunInd true

def Term.subst' (e : Term Γ t) (σ : Subst Γ Δ) :
    {r : Term Δ t // IsVar e → IsRenaming σ → IsVar r } :=
  match e with
  | .var i => ⟨σ i, by sorry⟩
  | .app e₁ e₂ => ⟨.app (e₁.subst' σ).val (e₂.subst' σ).val, by sorry⟩
  | .lam e₁ =>
    let r := .lam (e₁.subst' (Fin.cases (.var 0) (fun i => ((σ i).subst' .shift).1))).1
    ⟨r, by sorry⟩
termination_by (if IsVar e then 0 else 1, if IsRenaming σ then 0 else 1, sizeOf e)
decreasing_by
  · sorry
  · sorry
  · sorry
  · sorry
  · simp [*]
    apply Prod.Lex.right'
    · grind
    apply Prod.Lex.right'
    · sorry
    · sorry

/--
error: Failed to realize constant Term.subst'.induct:
  Cannot derive functional induction principle (please report this issue)
    Internal error in `foldAndCollect`: Cannot reduce application of `fun n Γ n_1 Δ σ t₂ t₁ e x =>
      Classical.byContradiction
        (Lean.Grind.intro_with_eq (¬(if IsVar e = true then 0 else 1) ≤ 1) (2 ≤ if IsVar e = true then 0 else 1) False
          (Nat.not_le_eq (if IsVar e = true then 0 else 1) 1) fun h =>
          Or.casesOn (Lean.Grind.em (IsVar e = true))
            (fun h_1 =>
              id
                (Lean.Grind.Nat.unsat_le_lo (if IsVar e = true then 0 else 1) 0 2 Lean.Grind.rfl_true
                  (Lean.Grind.Nat.le_of_eq_1 (if IsVar e = true then 0 else 1) 0 (ite_cond_eq_true 0 1 (eq_true h_1)))
                  h))
            fun h_1 =>
            id
              (Lean.Grind.Nat.unsat_le_lo (if IsVar e = true then 0 else 1) 1 1 Lean.Grind.rfl_true
                (Lean.Grind.Nat.le_of_eq_1 (if IsVar e = true then 0 else 1) 1 (ite_cond_eq_false 0 1 (eq_false h_1)))
                (Lean.Grind.Nat.ro_lo_2 1 0 (if IsVar e = true then 0 else 1) 1 2 Lean.Grind.rfl_true (Nat.le_refl 1)
                  h)))` in:
      (fun n Γ n_1 Δ σ t₂ t₁ e x =>
          Classical.byContradiction
            (Lean.Grind.intro_with_eq (¬(if IsVar e = true then 0 else 1) ≤ 1) (2 ≤ if IsVar e = true then 0 else 1)
              False (Nat.not_le_eq (if IsVar e = true then 0 else 1) 1) fun h =>
              Or.casesOn (Lean.Grind.em (IsVar e = true))
                (fun h_1 =>
                  id
                    (Lean.Grind.Nat.unsat_le_lo (if IsVar e = true then 0 else 1) 0 2 Lean.Grind.rfl_true
                      (Lean.Grind.Nat.le_of_eq_1 (if IsVar e = true then 0 else 1) 0
                        (ite_cond_eq_true 0 1 (eq_true h_1)))
                      h))
                fun h_1 =>
                id
                  (Lean.Grind.Nat.unsat_le_lo (if IsVar e = true then 0 else 1) 1 1 Lean.Grind.rfl_true
                    (Lean.Grind.Nat.le_of_eq_1 (if IsVar e = true then 0 else 1) 1
                      (ite_cond_eq_false 0 1 (eq_false h_1)))
                    (Lean.Grind.Nat.ro_lo_2 1 0 (if IsVar e = true then 0 else 1) 1 2 Lean.Grind.rfl_true
                      (Nat.le_refl 1) h))))
        n✝² Γ n✝ Δ σ t₂✝ t₁✝ e✝ x✝¹
---
error: Unknown constant `Term.subst'.induct`
-/
#guard_msgs(pass trace, all) in
#print Term.subst'.induct
