constant A : Type.{1}
constant a : A
constant g : A → A
constant f : A → A → A

(*
local f     = Const("f")
local g     = Const("g")
local comma = name(",")
function parse_pair()
  local p1 = parser.parse_expr()
  parser.check_token_next(comma, "invalid pair, ',' expected")
  print("line: " .. tostring(parser.pos()))
  local p2 = parser.parse_expr()
  return f(p1, p2)
end

local lbracket = name("[")
local rbracket = name("]")
function parse_bracket()
   local l, c = parser.pos()
   parser.check_token_next(lbracket, "'[' expected")
   local r = parser.parse_expr()
   parser.check_token_next(rbracket, "']' expected")
   return parser.save_pos(g(r), l, c)
end
*)


notation `tst` A:(call parse_pair) := A
notation `simple` A:(call parse_bracket) `,` B:(call parse_bracket) := f A B
constant b : A
check g (tst (simple [b], [a]), a)
