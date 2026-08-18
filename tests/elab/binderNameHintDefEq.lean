module

public section

/-! `binderNameHint`'s `.abbrev` reducibility hints make a definitional comparison unfold the
marker before its payload, so a marked type compares against its payload in constant time. A
marker with regular reducibility hints (`myHint` below) unfolds after the payload, and the
comparison walks the payload's whole reduction chain instead. -/

def W : Nat → Prop
  | 0 => True
  | n+1 => W n

@[simp ↓, expose, implicit_reducible]
def myHint {α : Sort u} {β : Sort v} {γ : Sort w} (_v : α) (_binder : β) (e : γ) : γ := e

-- The marker unfolds first: constant time, within a small heartbeat budget.
set_option maxHeartbeats 400 in
example : binderNameHint 0 (fun n : Nat => n) (W 100000) = W 100000 := rfl

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
set_option maxHeartbeats 400 in
example : myHint 0 (fun n : Nat => n) (W 100000) = W 100000 := rfl
