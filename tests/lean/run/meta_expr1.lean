import meta
open unsigned list

vm_eval expr.app (expr.app (expr.const "f" []) (expr.mk_var 1)) (expr.const "a" [])
