import Std.WP

open Lean.Order Std.Internal.Order

/-! ## Carrier `Prop` -/

example (q : Prop) : ¬ (⨆ r, (⌜some false = some r⌝ : Prop) ⊓ (r = false ∧ q)) → ¬ q := by grind

example (n : Nat) (p : Nat → Prop) (hn : 3 < n) :
    (⨅ i, ⌜i < n⌝ ⇨ ⨆ j, (⌜j = i + 1⌝ ⊓ p j : Prop)) ⊑ p 4 ⊔ ⊥ := by grind

/-! ## Single-state assertions -/

section
variable {σ : Type}

example (P : σ → Prop) (Q : Nat → σ → Prop) (a b : Nat) (h : P ⊑ Q a) :
    ⌜a < b⌝ ⊓ P ⊑ ⨆ n, ⌜n < b⌝ ⊓ Q n := by grind

example (P : σ → Prop) (Q R : Nat → σ → Prop) (s : σ) (h : (P ⊓ ⨅ n, Q n ⇨ R n) s)
    (hQ : Q 2 s) : (R 2 ⊔ ⊥) s ∧ P s := by grind

example (Q : Nat → σ → Prop) : (⨆ n, ⌜n = 3⌝ ⊓ Q n ⊔ ⊥ : σ → Prop) = Q 3 ⊓ ⊤ := by grind
end

/-! ## Multi-state assertions -/

section
variable {σ₁ σ₂ : Type}

example (P R : σ₁ → σ₂ → Prop) (Q : Nat → σ₁ → σ₂ → Prop) (b : Prop)
    (h₁ : P ⊑ R ⊔ ⊥) (h₂ : R ⊓ ⌜b⌝ ⊑ ⨅ n, Q n) (hb : b) : P ⊑ Q 7 := by grind

example (Q : Nat → σ₁ → σ₂ → Prop) (R : σ₁ → σ₂ → Prop) (s₁ : σ₁) (s₂ : σ₂)
    (h : (⨆ n, ⌜0 < n⌝ ⊓ (Q n ⇨ R)) s₁ s₂) (hQ : ∀ n, Q n s₁ s₂) : R s₁ s₂ := by grind
end

/-! ## Pairs of exception postconditions -/

section
variable {σ ε : Type}

example (E F : (ε → σ → Prop) × (Unit → σ → Prop)) (G : Nat → (ε → σ → Prop) × (Unit → σ → Prop))
    (p : Prop) (e : ε) (s : σ) (h₁ : (E ⊓ (F ⇨ ⌜p⌝)).1 e s) (hF : F.1 e s)
    (h₂ : (⨆ i, G i ⊔ ⊥).2 () s) : p ∧ E.1 e s ∧ ∃ i, (G i).2 () s := by grind

example (E F : (ε → σ → Prop) × (Unit → σ → Prop)) (p : Prop) (e : ε) (s : σ)
    (h : (E ⊔ F).1 e ⊑ ⌜p⌝ ⊓ (⊤ : (ε → σ → Prop) × (Unit → σ → Prop)).1 e) (hE : E.1 e s) :
    p := by grind
end

/-! ## Abstract complete lattice -/

section
variable {l : Type} [CompleteLattice l] [Heyting l]

example (x y : l) (Φ Ψ : Nat → l) (h : x ⊔ (⨆ i, Φ i) ⊑ y ⊓ ⨅ j, Ψ j) :
    Φ 3 ⊑ Ψ 5 ∧ x ⊑ y := by grind

example (p q r : Prop) (x y z : l) (h₁ : ⌜p⌝ ⊓ x ⊑ y ⊓ ⌜q⌝) (h₂ : (⊤ : l) ⊑ ⌜p⌝ ⇨ ⌜r⌝)
    (h₃ : ⊤ ⊑ y ⇨ z ⊔ ⊥) (hp : p) :
    x ⊑ y ∧ y ⊑ z ∧ ⊥ ⊑ z ∧ z ⊑ ⊤ ∧ (r ∨ (⊤ : l) ⊑ ⊥) := by grind

example (p q : Prop) (r : Nat → Prop) (x y : l) :
    (⌜True⌝ ⊓ x ⊔ (⨆ _ : Nat, ⊥) ⊔ ⌜False⌝ ⊓ y : l) = x ⊓ (⨅ _ : Nat, ⊤) ∧
    (⌜p⌝ ⊓ ⌜q⌝ ⊔ ⨆ i, ⌜r i⌝ : l) = ⌜(p ∧ q) ∨ ∃ i, r i⌝ := by grind

example {σ : Type} (P Q : σ → l) (p : Prop) (s : σ) (h : P ⊑ Q ⊓ ⌜p⌝) : P s ⊑ Q s := by grind
end

/-! ## Predicate transformers -/

example (P : Nat → Prop) (h : P 2) :
    ((do let s ← getThe Nat; if s < 5 then throwThe String "small" else set (s - 5)) :
      PredTrans (Nat → Prop) ((String → Prop) × PUnit) PUnit).apply
      (fun _ => ⌜True⌝ ⊓ P) (⊥, ⟨⟩) 7 := by grind

example (P : Nat → Prop) (h : P 4) :
    (tryCatchThe Nat (do let n ← pure 3; throwThe Nat (n + 1)) (fun e => pure (e * 2)) :
      PredTrans Prop ((Nat → Prop) × PUnit) Nat).apply
      (fun r => ⨆ k, ⌜r = 2 * k⌝ ⊓ P k) (⊥, ⟨⟩) := by grind

example (P : Nat → Prop) (h : P 2) :
    ((do let s ← get; if s < 5 then throw "small" else set (s - 5)) :
      PredTrans (Nat → Prop) ((String → Nat → Prop) × PUnit) PUnit).apply
      (fun _ => ⌜True⌝ ⊓ P) (⊥, ⟨⟩) 7 := by grind

example (Q : String → Nat → Prop) (h : Q "small" 3) :
    ((do let s ← get; if s < 5 then throw "small" else set (s - 5)) :
      PredTrans (Nat → Prop) ((String → Nat → Prop) × PUnit) PUnit).apply
      (fun _ => ⊥) (Q, ⟨⟩) 3 := by grind

example (P : Nat → Prop) (h : P 4) :
    (tryCatch (do let n ← pure 3; throw (n + 1)) (fun e => pure (e * 2)) :
      PredTrans Prop ((Nat → Prop) × PUnit) Nat).apply
      (fun r => ⨆ k, ⌜r = 2 * k⌝ ⊓ P k) (⊥, ⟨⟩) := by grind

example :
    ((do modify (· + 1); let s ← get; let t ← read; pure (s + t)) :
      PredTrans (Nat → Prop) PUnit Nat).apply
      (fun r s => ⌜r = 10⌝ ⊓ ⌜s = 5⌝) ⟨⟩ 4 := by grind
