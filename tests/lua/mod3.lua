local env = environment()
env = add_decl(env, mk_constant_assumption("A", Type))
env:export("mod3_mod.olean")
