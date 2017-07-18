namespace semantics
  inductive com
  | seq (c₁ c₂ : com)
  constant state : Type
  inductive smallstep : com × state → com × state → Prop
  | seq1 (c₁ c₂ σ c₁' σ') : smallstep ⟨c₁, σ⟩ ⟨c₂, σ'⟩ → smallstep ⟨com.seq c₁ c₂, σ⟩ ⟨com.seq c₁' c₂, σ'⟩

  lemma deterministic_aux (c σ c'₁ c'₂ σ'₁ σ'₂) (h₁ : smallstep ⟨c, σ⟩ ⟨c'₁, σ'₁⟩)
    (h₂ : smallstep ⟨c, σ⟩ ⟨c'₂, σ'₂⟩) : (c'₁, σ'₁) = (c'₂, σ'₂) :=
  begin
    induction h₁ generalizing c'₂ σ'₂,
  end
end semantics
