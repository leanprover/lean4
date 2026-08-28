macro "👉" t:(ppSpace ident) : term => `($t)
macro "👈" t:(lookahead(term) ident ppSpace) : term => `($t)
