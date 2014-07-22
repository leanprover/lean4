print(mk_expr_placeholder())
assert(not placeholder_type(mk_expr_placeholder()))
assert(placeholder_type(mk_expr_placeholder(Prop)) == Prop)
assert(is_placeholder(mk_expr_placeholder(Prop)))
