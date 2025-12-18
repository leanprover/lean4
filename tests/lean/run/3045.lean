namespace X
def test := "test"
end X

namespace Y

namespace X end X

-- We want to open `X`, not `Y.X`
open _root_.X  -- should not produce `unknown namespace '_root_.X'`
/--
info: X.test : String
-/
#guard_msgs in
#check test
