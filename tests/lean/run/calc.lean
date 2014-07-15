import standard
using num

namespace foo
  variable le : num → num → Bool
  axiom le_trans {a b c : num} : le a b → le b c → le a c
  calc_trans le_trans
  infix `≤`:50 := le
end

namespace foo
  theorem T {a b c d : num} : a ≤ b → b ≤ c → c ≤ d → a ≤ d
  := assume H1 H2 H3,
     calc a  ≤ b : H1
         ... ≤ c : H2
         ... ≤ d : H3
end
