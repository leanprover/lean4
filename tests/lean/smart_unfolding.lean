constant n : nat
#reduce n + (nat.succ n)

set_option type_context.smart_unfolding false
#reduce n + (nat.succ n)
