prelude constant A : Type.{1}
constant f : A → A → A
constant g : A → A → A
precedence `+` : 65
infixl + := f
infixl + := g
constant a : A
constant b : A
print raw a+b -- + is overloaded
check fun (h : A → A → A)
          (infixl + := h), -- Like local declarations, local notation "shadows" global one.
      a+b
