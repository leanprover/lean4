variable A : Type.{1}
variable f : A → A → A
variable g : A → A → A
precedence `+` : 65
infixl + := f
infixl + := g
variable a : A
variable b : A
print raw a+b -- + is overloaded
check fun (h : A → A → A)
          (infixl + := h), -- Like local declarations, local notation "shadows" global one.
      a+b