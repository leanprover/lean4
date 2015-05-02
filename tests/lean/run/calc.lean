import data.num


namespace foo
  constant le : num → num → Prop
  axiom le_trans {a b c : num} : le a b → le b c → le a c
  attribute le_trans [trans]
  infix `≤` := le
end foo

namespace foo
  theorem T {a b c d : num} : a ≤ b → b ≤ c → c ≤ d → a ≤ d
  := assume H1 H2 H3,
     calc a  ≤ b : H1
         ... ≤ c : H2
         ... ≤ d : H3
end foo
