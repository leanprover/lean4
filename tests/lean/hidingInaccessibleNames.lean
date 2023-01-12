def f : (xs : List Nat) → Nat → xs ≠ [] → Nat
  | [], _, _ => _
  | [a,b], _, _ => _
  | _, _, _ => _

set_option pp.inaccessibleNames true in
def f' : (xs : List Nat) → Nat → xs ≠ [] → Nat
  | [], _, _ => _ -- TODO: figure out why hyp `Ne (α := List Nat) x✝² []` needs α
  | [a,b], _, _ => _
  | _, _, _ =>  _

theorem ex1 : p ∨ q → q ∨ p := by
  intro h
  cases h
  trace_state
  apply Or.inr
  assumption
  apply Or.inl
  assumption
  done

theorem ex2 : {p : Prop} → [Decidable p] → p → decide p = true
  | _, ⟨true, _⟩, _   => _
  | _, ⟨false, h₁⟩, h₂ => h₁.2 h₂

theorem ex3 : ∀ {c d : Char}, c = d → c.val = d.val
  | _, _, rfl => _
