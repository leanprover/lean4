m1 = mk_metavar("a")
print(m1)
m2 = mk_metavar("b", local_context(mk_inst(1, Const("a")), local_context()))
print(m2)
