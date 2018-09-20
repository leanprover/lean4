set_option trace.compiler.lcnf true
set_option pp.binder_types false

def tst1 (a : nat) : nat :=
@nat.cases_on (λ _, nat) a 0 id
