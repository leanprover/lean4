

def A.foo {α : Type} [Add α] (a : α) : α × α :=
(a, a + a)

def B.foo {α : Type} (a : α) : α × α :=
(a, a)

open A
open B

set_option trace.Meta.synthInstance true
-- `foo` is overloaded, the case `A.foo` is discarded because we don't have an instance `[Add String]`.
-- However, we still want to see the trace since we used trace.Meta.synthInstance
#check foo "hello"

theorem ex : foo true = (true, true) :=
rfl
