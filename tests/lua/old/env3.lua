env = environment()
env:add_var("N", Type())
env:add_var("x", Const("N"))
print(env)
