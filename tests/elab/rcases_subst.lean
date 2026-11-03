/-!
Goals produced by `rcases` when expressions obtained earlier in the pattern must be translated
through later `cases` and `subst` steps: later targets reverted by an earlier split, cleared
hypotheses, `rfl` patterns, alternatives, and quotients.
-/

set_option pp.proofs true
set_option linter.unusedVariables false

-- Later targets depend on earlier ones: splitting an earlier target reverts and reintroduces them.
example (p : Nat × Nat) (h : p.1 = p.2) : True := by
  obtain ⟨⟨a, b⟩, h'⟩ := p, h
  trace_state
  trivial

example (n : Nat) (v : Fin (n + 1)) (h : v.val = 0) : True := by
  obtain ⟨_ | m, w, h'⟩ := n, v, h
  all_goals trace_state
  all_goals trivial

-- Clears recorded before a later split that reverts the cleared hypothesis.
example (p q : Nat × Nat) (h : q.1 = p.1) : True := by
  obtain ⟨-, ⟨c, d⟩⟩ := p, q
  trace_state
  trivial

example (p q : Nat × Nat) (h : q.1 = p.1) : True := by
  obtain ⟨⟨c, d⟩, -⟩ := q, p
  trace_state
  trivial

example (p : Nat × Nat) (h : p.1 = 0) : True := by
  obtain ⟨⟨a, -⟩, -⟩ := p, h
  trace_state
  trivial

-- `rfl` before and after splits.
example (h : ∃ x y : Nat, x = y ∧ y = 3) : True := by
  obtain ⟨x, y, rfl, rfl⟩ := h
  trace_state
  trivial

example (n : Nat) (h : n = 3 ∧ ∃ m : Nat, m = n) (k : n < 5) : True := by
  obtain ⟨rfl, m, hm⟩ := h
  trace_state
  trivial

example (n : Nat) (h : n = 3) (p : Fin n × Nat) : True := by
  obtain ⟨rfl, ⟨i, j⟩⟩ := h, p
  trace_state
  trivial

-- Alternatives followed by further splits in each branch.
example (h : (∃ a : Nat, a = 0 ∧ True) ∨ (∃ b : Nat, b = 1 ∧ ∃ c : Nat, c = b)) (z : Nat) : True := by
  obtain ⟨a, ha, -⟩ | ⟨b, hb, c, hc⟩ := h
  all_goals trace_state
  all_goals trivial

-- Quotients.
example (x : Quot fun _ _ : Nat => True) (h : x = x) (y : Nat × Nat) : True := by
  obtain ⟨⟨z⟩, ⟨u, v⟩⟩ := x, y
  trace_state
  trivial

-- Named targets: the equation hypothesis is recorded before the splits.
example (p : Nat × (Nat × Nat)) : True := by
  rcases hp : p with ⟨a, b, c⟩
  trace_state
  trivial

example (n : Nat) (p : Fin n × Nat) : True := by
  rcases hn : n, hp : p with ⟨_ | m, ⟨i, j⟩⟩
  all_goals trace_state
  all_goals trivial

-- A dependent chain.
example (h : ∃ a : Nat, a = 1 ∧ ∃ b : Nat, b = a + 1 ∧ ∃ c : Nat, c = b + 1 ∧ True) : True := by
  obtain ⟨a, ha, b, hb, c, hc, -⟩ := h
  trace_state
  trivial

-- A no-value obtain.
example : True := by
  obtain ⟨n, hn, -⟩ : ∃ n : Nat, n = 0 ∧ True
  · exact ⟨0, rfl, trivial⟩
  trace_state
  trivial
