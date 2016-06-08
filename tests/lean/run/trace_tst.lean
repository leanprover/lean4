open nat

vm_eval trace "step1" (λ u, trace "hello" (λ u, succ 3))
