import Lean.Elab.Tactic.Basic

set_option linter.missingDocs false

example (x : α × β × γ) : True := by
  rcases x with ⟨a, b, c⟩
  guard_hyp a : α
  guard_hyp b : β
  guard_hyp c : γ
  trivial

example (x : α × β × γ) : True := by
  rcases x with ⟨(a : α) : id α, -, c : id γ⟩
  guard_hyp a : α
  fail_if_success have : β := by assumption
  guard_hyp c : id γ
  trivial

example (x : (α × β) × γ) : True := by
  fail_if_success rcases x with ⟨_a, b, c⟩
  fail_if_success rcases x with ⟨⟨a:β, b⟩, c⟩
  rcases x with ⟨⟨a:α, b⟩, c⟩
  guard_hyp a : α
  guard_hyp b : β
  guard_hyp c : γ
  trivial

example : @Inhabited.{1} α × Option β ⊕ γ → True := by
  rintro (⟨⟨a⟩, _ | b⟩ | c)
  · guard_hyp a : α; trivial
  · guard_hyp a : α; guard_hyp b : β; trivial
  · guard_hyp c : γ; trivial

example : cond false Nat Int → cond true Int Nat → Nat ⊕ Unit → True := by
  rintro (x y : Int) (z | u)
  · guard_hyp x : Int; guard_hyp y : Int; guard_hyp z : Nat; trivial
  · guard_hyp x : Int; guard_hyp y : Int; guard_hyp u : Unit; trivial

example (x y : Nat) (h : x = y) : True := by
  rcases x with _|⟨⟩|z
  · guard_hyp h :ₛ 0 = y; trivial
  · guard_hyp h :ₛ 0 + 1 = y; trivial
  · guard_hyp z : Nat
    guard_hyp h :ₛ z + 1 + 1 = y; trivial

example (h : x = 3) (h₂ : x < 4) : x < 4 := by
  rcases h with ⟨⟩
  guard_hyp h₂ : 3 < 4; guard_target = 3 < 4; exact h₂

example (h : x = 3) (h₂ : x < 4) : x < 4 := by
  rcases h with rfl
  guard_hyp h₂ : 3 < 4; guard_target = 3 < 4; exact h₂

example (h : 3 = x) (h₂ : x < 4) : x < 4 := by
  rcases h with ⟨⟩
  guard_hyp h₂ : 3 < 4; guard_target = 3 < 4; exact h₂

example (h : 3 = x) (h₂ : x < 4) : x < 4 := by
  rcases h with rfl
  guard_hyp h₂ : 3 < 4; guard_target = 3 < 4; exact h₂

example (s : α ⊕ Empty) : True := by
  rcases s with s|⟨⟨⟩⟩
  guard_hyp s : α; trivial

example : True := by
  obtain ⟨n : Nat, _h : n = n, -⟩ : ∃ n : Nat, n = n ∧ True
  · exact ⟨0, rfl, trivial⟩
  trivial

example : True := by
  obtain (h : True) | ⟨⟨⟩⟩ : True ∨ False
  · exact Or.inl trivial
  guard_hyp h : True; trivial

example : True := by
  obtain h | ⟨⟨⟩⟩ : True ∨ False := Or.inl trivial
  guard_hyp h : True; trivial

example : True := by
  obtain ⟨h, h2⟩ := And.intro trivial trivial
  guard_hyp h : True; guard_hyp h2 : True; trivial

example : True := by
  fail_if_success obtain ⟨h, h2⟩
  trivial

example (x y : α × β) : True := by
  rcases x, y with ⟨⟨a, b⟩, c, d⟩
  guard_hyp a : α; guard_hyp b : β
  guard_hyp c : α; guard_hyp d : β
  trivial

example (x y : α ⊕ β) : True := by
  rcases x, y with ⟨a|b, c|d⟩
  · guard_hyp a : α; guard_hyp c : α; trivial
  · guard_hyp a : α; guard_hyp d : β; trivial
  · guard_hyp b : β; guard_hyp c : α; trivial
  · guard_hyp b : β; guard_hyp d : β; trivial

example (i j : Nat) : (Σ' x, i ≤ x ∧ x ≤ j) → i ≤ j := by
  intro h
  rcases h' : h with ⟨x, h₀, h₁⟩
  guard_hyp h' : h = ⟨x, h₀, h₁⟩
  apply Nat.le_trans h₀ h₁

example (x : Quot fun _ _ : α => True) (h : x = x): x = x := by
  rcases x with ⟨z⟩
  guard_hyp z : α
  guard_hyp h : Quot.mk (fun _ _ => True) z = Quot.mk (fun _ _ => True) z
  guard_target = Quot.mk (fun _ _ => True) z = Quot.mk (fun _ _ => True) z
  exact h

example (n : Nat) : True := by
  obtain _one_lt_n | _n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := Nat.lt_or_ge 1 (n + 1)
  {trivial}; trivial

example (n : Nat) : True := by
  obtain _one_lt_n | (_n_le_one : n + 1 ≤ 1) := Nat.lt_or_ge 1 (n + 1)
  {trivial}; trivial

open Lean Elab Tactic in
/-- Asserts that the goal has `n` hypotheses. Used for testing. -/
elab "check_num_hyps " n:num : tactic => liftMetaMAtMain fun _ => do
  -- +1 because the _example recursion decl is in the list
  guard $ (← getLCtx).foldl (fun i _ => i+1) 0 = n.1.toNat + 1

example (h : ∃ x : Nat, x = x ∧ 1 = 1) : True := by
  rcases h with ⟨-, _⟩
  check_num_hyps 0
  trivial

example (h : ∃ x : Nat, x = x ∧ 1 = 1) : True := by
  rcases h with ⟨-, _, h⟩
  check_num_hyps 1
  guard_hyp h : 1 = 1
  trivial

example (h : True ∨ True ∨ True) : True := by
  rcases h with - | - | -
  iterate 3 · check_num_hyps 0; trivial

example (h : True ∨ True ∨ True) : True := by
  rcases h with -|-|-
  iterate 3 · check_num_hyps 0; trivial

example : Bool → False → True
| false => by rintro ⟨⟩
| true => by rintro ⟨⟩

example : (b : Bool) → cond b False False → True := by
  rintro ⟨⟩ ⟨⟩

structure Baz {α : Type _} (f : α → α) : Prop where
  [inst : Nonempty α]
  h : f ∘ f = id

example {α} (f : α → α) (h : Baz f) : True := by rcases h with ⟨_⟩; trivial

example {α} (f : α → α) (h : Baz f) : True := by rcases h with @⟨_, _⟩; trivial

inductive Test : Nat → Prop
  | a (n) : Test (2 + n)
  | b {n} : n > 5 → Test (n * n)

example {n} (h : Test n) : n = n := by
  have : True := by
    rcases h with (a | b)
    · guard_hyp a : Nat
      trivial
    · guard_hyp b : ‹Nat› > 5
      trivial
  · rcases h with (a | @⟨n, b⟩)
    · guard_hyp a : Nat
      trivial
    · guard_hyp b : n > 5
      trivial

example (h : a ≤ 2 ∨ 2 < a) : True := by
  obtain ha1 | ha2 : a ≤ 2 ∨ 3 ≤ a := h
  · guard_hyp ha1 : a ≤ 2; trivial
  · guard_hyp ha2 : 3 ≤ a; trivial

example (h : a ≤ 2 ∨ 2 < a) : True := by
  obtain ha1 | ha2 : a ≤ 2 ∨ 3 ≤ a := id h
  · guard_hyp ha1 : a ≤ 2; trivial
  · guard_hyp ha2 : 3 ≤ a; trivial

example (a : Nat) : True := by
  rcases h : a with _ | n
  · guard_hyp h :ₛ a = 0; trivial
  · guard_hyp h :ₛ a = n + 1; trivial

inductive BaseType : Type where
  | one

inductive BaseTypeHom : BaseType → BaseType → Type where
  | loop : BaseTypeHom one one
  | id (X : BaseType) : BaseTypeHom X X

example : BaseTypeHom one one → Unit := by rintro ⟨_⟩ <;> constructor

axiom test_sorry {α} : α
example (b c : Nat) : True := by
  obtain rfl : b = c ^ 2 := test_sorry
  trivial

example (b c : Nat) : True := by
  obtain h : b = c ^ 2 := test_sorry
  subst h
  trivial
