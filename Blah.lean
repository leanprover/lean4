def SatisfiesM {m : Type u → Type v} {α} [Functor m] (p : α → Prop) (x : m α) : Prop :=
  ∃ x' : m {a // p a}, Subtype.val <$> x' = x

theorem SatisfiesM.and [Monad m] [LawfulMonad m] {x : m α} {p q : α → Prop}
    (hp : SatisfiesM p x) (hq : SatisfiesM q x) : SatisfiesM (fun r => p r ∧ q r) x := by
  obtain ⟨xsub_p, hsub_p⟩ := hp
  obtain ⟨xsub_q, hsub_q⟩ := hq
  subst x
  have sdlfkj_p := Subtype.property <$> xsub_p
  have sdlfkj_q := Subtype.property <$> xsub_q
  constructor
  case w => sorry
  case w => sorry



theorem SatisfiesM.imp [Functor m] [LawfulFunctor m] {x : m α}
    (h : SatisfiesM p x) (H : ∀ {a}, p a → q a) : SatisfiesM q x :=
  let ⟨x, h⟩ := h; ⟨(fun ⟨_, h⟩ => ⟨_, H h⟩) <$> x, by rw [← h, ← comp_map]; rfl⟩


theorem SatisfiesM.split_step [Functor m] [LawfulFunctor m] {x : m (ForInStep β)}
    {done : β → Prop} {yield : β → Prop}
    (hyield : SatisfiesM (∀ b', · = .yield b' → yield b') x)
    (hdone :  SatisfiesM (∀ b', · = .done b'  → done b') x) :
    SatisfiesM (fun r => (∃ b', r = .yield b' ∧ yield b') ∨ (∃ b', r = .done b' ∧ done b')) x := by
      obtain ⟨xsub_yld, hsub_yld⟩ := hyield
      obtain ⟨xsub_dn, hsub_dn⟩ := hdone
      subst x
      constructor
      case h =>
      case w =>
      exact ⟨(fun r => ⟨r,match r with | .yield b' => _ | .done b' => _⟩) <$> x, _⟩
