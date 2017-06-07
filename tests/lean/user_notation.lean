open lean (parser)
open lean.parser
open interactive
open tactic

reserve prefix `unquote! `:100
@[user_notation]
meta def unquote_macro (_ : parse $ tk "unquote!") (e : parse lean.parser.pexpr) : parser pexpr :=
↑(to_expr e >>= eval_expr pexpr)

#eval unquote! ``(1 + 1)

reserve infix ` +⋯+ `:65
@[user_notation]
meta def upto_notation (e₁ : parse lean.parser.pexpr) (_ : parse $ tk "+⋯+") (n₂ : ℕ) : parser pexpr :=
do n₁ ← ↑(to_expr e₁ >>= eval_expr nat),
   pure $ (n₂+1-n₁).repeat (λ i e, ``(%%e + %%(reflect $ n₁ + i))) ``(0)

#check 1 +⋯+ 10

@[user_notation]
meta def no_tk (e₁ : parse lean.parser.pexpr) := e₁

@[user_notation]
meta def no_parser (e₁ : parse $ tk "(") := e₁
