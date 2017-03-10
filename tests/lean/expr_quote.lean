meta def f (α a : expr) := ```(@id %%α %%a)

meta def f (α a : expr) := ```(@id (%%α : Type 2) %%a)

set_option pp.universes true
#print f
