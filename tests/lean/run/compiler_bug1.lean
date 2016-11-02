inductive stmt : Type
| switch : list (nat × stmt) → stmt → stmt
| nop    : stmt

meta def compile_cases_on_to_ir_expr : option stmt := do
do cs' ← return ([] : list (nat × stmt)),
   return (stmt.switch cs' stmt.nop)
