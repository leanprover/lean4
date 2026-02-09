namespace MySigma
  /-- We define a new `Sigma` -/
  def Sigma {α : Type u} (β : α → Type v)
    := String

  #reduce Σ a, a -- This should not reduce to `String`
end MySigma
