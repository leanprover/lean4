constant A : Type.{1}
constant a : A
constant g : A → A
constant f : A → A → A
precedence `|` : 0

(*
local f      = Const("f")
local g      = Const("g")
local bar    = name("|")
local rcurly = name("}")
local lcurly = name("{")
function parse_set()
  parser.check_token_next(lcurly, "'{' expected")
  local s  = parser.parse_binder()
  parser.check_token_next(bar, "'|' expected")
  local e  = parser.parse_scoped_expr(s)
  parser.check_token_next(rcurly, "'}' expected")
  print(e)
  return parser.abstract(s, g(e))
end
*)


notation `set` A:(call parse_set) := A
check set { x : A | f x x }
