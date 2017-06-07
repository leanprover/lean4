section
def {u} typer (α : Type u) := α
parameter n : ℕ

meta def blah (n : typer ℕ) : ℕ := n

#check blah
end
#check blah
