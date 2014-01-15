local env = get_environment()
assert(env:imported("kernel"))
assert(env:imported("Nat"))
assert(not env:imported("Real"))
print("before import Real")
env:import("Real")
print("after import Real")
assert(env:imported("Real"))
parse_lean_cmds([[
    variables a b c : Real
    check a + b + 0
]])
