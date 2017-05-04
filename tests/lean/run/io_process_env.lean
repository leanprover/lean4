import system.io
variable [io.interface]

#eval do
res ← io.cmd "printenv" ["foo"] none [("foo", "bar")],
when (res ≠ "bar\n") $ io.fail $ "unexpected value for foo: " ++ res