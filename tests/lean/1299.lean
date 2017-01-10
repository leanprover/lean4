open tactic expr

def d1 : true = true := by do
trace (("a", "a")),
prt ← to_expr `(true = true),
add_decl (declaration.ax `new_ax [] prt),
l ← to_expr `(new_ax),
apply l

check d1
print d1

theorem d2 : true = true := by do
trace (("a", "a")),
prt ← to_expr `(true = true),
add_decl (declaration.ax `new_ax2 [] prt),
l ← to_expr `(new_ax2),
apply l

print d2
