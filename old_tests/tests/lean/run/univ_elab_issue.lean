meta def foo (ex_lst : list name) (e : expr) : list name :=
e^.fold [] (λ c _ l, l)
