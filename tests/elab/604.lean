def foo {{u : Unit}} : Unit := u
#check foo -- foo : ⦃u : Unit⦄ → Unit
#check (foo : ∀ {{u : Unit}}, Unit)

def bla {u : Unit} : Unit := u

#check bla

#check (bla : ∀ {u : Unit}, Unit)
