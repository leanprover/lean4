/- Basic rewriting with eq and generic congruence, with no conditionals -/

namespace test_congr

constants a b c : nat
axiom H1 : a = b
axiom H2 : a = c

attribute H1 [simp]
attribute H2 [simp]

#simplify eq env 0 a -- c

attribute H1 [simp]

#simplify eq env 0 a -- b

attribute H1 [simp] [priority std.priority.default+1]
attribute H2 [simp]

#simplify eq env 0 a -- b

attribute H2 [simp] [priority std.priority.default+2]
attribute H1 [simp] [priority std.priority.default+1]

#simplify eq env 0 a -- c

end test_congr
