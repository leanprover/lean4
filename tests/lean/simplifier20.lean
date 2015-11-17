/- Basic rewriting with eq and generic congruence, with no conditionals -/

namespace test_congr

constants a b c : nat
axiom H1 : a = b
axiom H2 : a = c

attribute H1 [simp]
attribute H2 [simp]

#simplify eq env 0 a -- c

attribute H1 [simp] [priority 20000]

#simplify eq env 0 a -- b

attribute H2 [simp] [priority 30000]

#simplify eq env 0 a -- c

attribute H1 [simp] [priority 20000]

#simplify eq env 0 a -- c

attribute H2 [simp] [priority 20000]
attribute H1 [simp] [priority 20001]

#simplify eq env 0 a -- b

end test_congr
