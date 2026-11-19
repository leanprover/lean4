section setup

variable {α : Sort u}
variable {β : α → Sort v}
variable {γ : Sort w}

def callsOn (P : α → Prop) (F : (∀ y, β y) → γ) :=
  ∃ (F': (∀ y, P y → β y) → γ), ∀ f, F' (fun y _ => f y) = F f

variable (R : α → α → Prop)
variable (F : (∀ y, β y) → (∀ x, β x))

local infix:50 " ≺ " => R

def recursesVia : Prop := ∀ x, callsOn (· ≺ x) (fun f => F f x)

noncomputable def fix (wf : WellFounded R) (h : recursesVia R F) : (∀ x, β x) :=
  wf.fix (fun x => (h x).choose)

def fix_eq (wf : WellFounded R) h x : fix R F wf h x = F (fix R F wf h) x := by
  unfold fix
  rw [wf.fix_eq]
  apply (h x).choose_spec

theorem callsOn_base (y : α) (hy : P y) : callsOn P (fun (f : ∀ x, β x) => f y) := by
  exists fun f => f y hy
  intros; rfl

@[simp]
theorem callsOn_const (x : γ) : callsOn P (fun (_ : ∀ x, β x) => x) :=
  ⟨fun _ => x, fun _ => rfl⟩

theorem callsOn_app
  {γ₁ : Sort uu} {γ₂ : Sort ww}
  (F₁ :  (∀ y, β y) → γ₂ → γ₁) -- can this also support dependent types?
  (F₂ :  (∀ y, β y) → γ₂)
  (h₁ : callsOn P F₁)
  (h₂ : callsOn P F₂) :
  callsOn P (fun f => F₁ f (F₂ f)) := by
  obtain ⟨F₁', h₁⟩ := h₁
  obtain ⟨F₂', h₂⟩ := h₂
  exists (fun f => F₁' f (F₂' f))
  intros; simp_all

theorem callsOn_lam
  {γ₁ : Sort uu}
  (F : γ₁ → (∀ y, β y) → γ) -- can this also support dependent types?
  (h : ∀ x, callsOn P (F x)) :
  callsOn P (fun f x => F x f) := by
  exists (fun f x => (h x).choose f)
  intro f
  ext x
  apply (h x).choose_spec

theorem callsOn_app2
  {γ₁ : Sort uu} {γ₂ : Sort ww}
  (g : γ₁ → γ₂ → γ)
  (F₁ :  (∀ y, β y) → γ₁) -- can this also support dependent types?
  (F₂ :  (∀ y, β y) → γ₂)
  (h₁ : callsOn P F₁)
  (h₂ : callsOn P F₂) :
  callsOn P (fun f => g (F₁ f) (F₂ f)) := by
  apply_rules [callsOn_app, callsOn_const]

theorem callsOn_map (δ : Type uu) (γ : Type ww)
    (P : α → Prop) (F : (∀ y, β y) → δ → γ) (xs : List δ)
    (h : ∀ x, x ∈ xs → callsOn P (fun f => F f x)) :
  callsOn P (fun f => xs.map (fun x => F f x)) := by
  suffices callsOn P (fun f => xs.attach.map (fun ⟨x, h⟩ => F f x)) by
    simpa
  apply callsOn_app
  · apply callsOn_app
    · apply callsOn_const
    · apply callsOn_lam
      intro ⟨x', hx'⟩
      dsimp
      exact (h x' hx')
  · apply callsOn_const

end setup

section examples

structure Tree (α : Type u) where
  val : α
  cs : List (Tree α)

noncomputable def List.map' (f : α → β) : List α → List β :=
  fix (sizeOf · < sizeOf ·) (fun map l => match l with | [] => [] | x::xs => f x :: map xs)
    (InvImage.wf (sizeOf ·) WellFoundedRelation.wf) <| by
  intro l
  dsimp only
  cases l -- check that the predicate of `callsOn` is appropriately refined
  · simp
  · simp only [cons.sizeOf_spec, sizeOf_default, Nat.add_zero]
    apply callsOn_app2
    · apply callsOn_const
    · apply callsOn_base
      simp

noncomputable def Tree.map (f : α → β) : Tree α → Tree β :=
  fix (sizeOf · < sizeOf ·) (fun map t => ⟨f t.val, t.cs.map map⟩)
    (InvImage.wf (sizeOf ·) WellFoundedRelation.wf) <| by
  intro ⟨v, cs⟩
  dsimp only
  apply callsOn_app2
  · apply callsOn_const
  · apply callsOn_map
    intro t' ht'
    apply callsOn_base
    decreasing_trivial


end examples
