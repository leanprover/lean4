inductive term
| const (c : string)                   : term
| app   (fn : string) (ts : list term) : term

mutual inductive is_rename, is_rename_lst
with is_rename : term → string → string → term → Prop
| const_eq (c₁ c₂) : is_rename (term.const c₁) c₁ c₂ (term.const c₂)
| const_ne (c₁ c₂ c₃) (hne : c₁ ≠ c₂) : is_rename (term.const c₁) c₂ c₃ (term.const c₁)
| app      (fn c₁ c₂ ts₁ ts₂) (h₁ : is_rename_lst ts₁ c₁ c₂ ts₂) : is_rename (term.app fn ts₁) c₁ c₂ (term.app fn ts₂)
with is_rename_lst : list term → string → string → list term → Prop
| nil  (c₁ c₂) : is_rename_lst [] c₁ c₂ []
| cons (t₁ ts₁ t₂ ts₂ c₁ c₂) (h₁ : is_rename t₁ c₁ c₂ t₂) (h₂ : is_rename_lst ts₁ c₁ c₂ ts₂) : is_rename_lst (t₁::ts₁) c₁ c₂ (t₂::ts₂)

mutual def term.ind, term_list.ind
  (p : term → Prop) (ps : list term → Prop)
  (h₁ : ∀ c, p (term.const c))
  (h₂ : ∀ fn ts, ps ts → p (term.app fn ts))
  (h₃ : ps [])
  (h₄ : ∀ t ts, p t → ps ts → ps (t::ts))
with term.ind : ∀ t : term, p t
| (term.const c)   := h₁ c
| (term.app fn ts) := h₂ fn ts (term_list.ind ts)
with term_list.ind : ∀ ts : list term, ps ts
| []      := h₃
| (t::ts) := h₄ t ts (term.ind t) (term_list.ind ts)

lemma term.ind_on
  (p : term → Prop) (ps : list term → Prop)
  (t : term)
  (h₁ : ∀ c, p (term.const c))
  (h₂ : ∀ fn ts, ps ts → p (term.app fn ts))
  (h₃ : ps [])
  (h₄ : ∀ t ts, p t → ps ts → ps (t::ts)) : p t :=
term.ind p ps h₁ h₂ h₃ h₄ t

lemma is_rename_det : ∀ t₁ t₂ t₂' c₁ c₂, is_rename t₁ c₁ c₂ t₂ → is_rename t₁ c₁ c₂ t₂' → t₂ = t₂' :=
begin
  intro t₁,
  apply term.ind_on
    (λ t₁ : term,       ∀ t₂ t₂' c₁ c₂, is_rename t₁ c₁ c₂ t₂ → is_rename t₁ c₁ c₂ t₂' → t₂ = t₂')
    (λ ts₁ : list term, ∀ ts₂ ts₂' c₁ c₂, is_rename_lst ts₁ c₁ c₂ ts₂ → is_rename_lst ts₁ c₁ c₂ ts₂' → ts₂ = ts₂')
    t₁,
  { intros c₁ t₂ t₂' c₁' c₂ h₁ h₂,
    cases h₁; cases h₂; trace_state; { refl <|> contradiction }  },
  { intros fn ts ih t₂ t₂' c₁ c₂ h₁ h₂, cases h₁; cases h₂, trace_state,
    have := ih _ _ _ _ h₁_h₁ h₂_h₁,
    simp [*] },
  { intros ts₂ ts₂' c₁ c₂ h₁ h₂,
    cases h₁; cases h₂; refl },
  { intros t ts ih₁ ih₂ ts₂ ts₂' c₁ c₂ h₁ h₂,
    cases h₁; cases h₂,
    have := ih₁ _ _ _ _ h₁_h₁ h₂_h₁,
    have := ih₂ _ _ _ _ h₁_h₂ h₂_h₂,
    simp [*] }
end

mutual def is_rename.ind, is_rename_lst.ind
  (p  : ∀ {t₁ c₁ c₂ t₂}, is_rename t₁ c₁ c₂ t₂ → Prop)
  (ps : ∀ {ts₁ c₁ c₂ ts₂}, is_rename_lst ts₁ c₁ c₂ ts₂ → Prop)
  (h₁ : ∀ (c₁ c₂ : string), p (is_rename.const_eq c₁ c₂))
  (h₂ : ∀ (c₁ c₂ c₃ : string) (hne : c₁ ≠ c₂), p (is_rename.const_ne c₁ c₂ c₃ hne))
  (h₃ : ∀ (fn c₁ c₂ ts₁ ts₂ h) (ih : ps h), p (is_rename.app fn c₁ c₂ ts₁ ts₂ h))
  (h₄ : ∀ (c₁ c₂ : string), ps (is_rename_lst.nil c₁ c₂))
  (h₅ : ∀ (t₁ ts₁ t₂ ts₂ c₁ c₂ h₁ h₂) (ih₁ : p h₁) (ih₂ : ps h₂), ps (is_rename_lst.cons t₁ ts₁ t₂ ts₂ c₁ c₂ h₁ h₂))
with is_rename.ind   : ∀ (t₁ c₁ c₂ t₂) (h : is_rename t₁ c₁ c₂ t₂), p h
| (term.const c) :=
  begin
    intros c₁ c₂ t₂ hr,
    cases t₂; cases hr,
    { apply h₁ },
    { apply h₂, assumption }
  end
| (term.app fn ts₁) :=
  have ih : ∀ (c₁ c₂ ts₂) (h : is_rename_lst ts₁ c₁ c₂ ts₂), ps h, from is_rename_lst.ind ts₁,
  begin
    intros c₁ c₂ t₂ hr,
    cases t₂; cases hr,
    apply h₃, apply ih, assumption
  end

with is_rename_lst.ind  : ∀ (ts₁ c₁ c₂ ts₂) (h : is_rename_lst ts₁ c₁ c₂ ts₂), ps h
| [] :=
  begin
    intros c₁ c₂ ts₂ hr,
    cases ts₂; cases hr, apply h₄
  end
| (t₁::ts₁) :=
  have ih₁ : ∀ (c₁ c₂ t₂) (h : is_rename t₁ c₁ c₂ t₂), p h, from is_rename.ind t₁,
  have ih₂ : ∀ (c₁ c₂ ts₂) (h : is_rename_lst ts₁ c₁ c₂ ts₂), ps h, from is_rename_lst.ind ts₁,
  begin
    intros c₁ c₂ ts₂ hr,
    cases ts₂; cases hr,
    fapply h₅, exact hr_h₁, exact hr_h₂,
    exact ih₁ _ _ _ hr_h₁,
    exact ih₂ _ _ _ hr_h₂
  end
