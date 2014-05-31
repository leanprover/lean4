local env = environment()
env = add_decl(env, mk_var_decl("A", Type))
env:export("mod3_mod.olean")
