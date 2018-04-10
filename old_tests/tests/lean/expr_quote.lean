meta def f (α a : expr) := `(@id %%α %%a)

meta def g (α a : expr) := `(@id (%%α : Type 2) %%a)

set_option pp.universes true
#print g
