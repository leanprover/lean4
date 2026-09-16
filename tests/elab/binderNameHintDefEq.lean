module

public section

/-! `binderNameHint` carries `.abbrev` reducibility hints so that definitional comparison unfolds
it eagerly. Consider

    myHint 0 (fun n => n) (W 100000)  =?=  W 100000

Here, `isDefEq` and the kernel both see a constant applied to arguments and must make a choice
which constant to unfold first. For `ReducibilityHints.regular`, the choice is to unfold `W`
because it has greater *height* than height 1 for `myHint`, and this problem recurs on the order
of 100000 times. By contrast, for `.abbrev`, the gadget is chosen and the defeq succeeds in
constant time.

`myHint` below replicates `binderNameHint` with `.regular` hints: the comparison through it
exceeds the recursion depth, while the one through `binderNameHint` succeeds within a small
heartbeat budget. -/

def W : Nat → Prop
  | 0 => True
  | n+1 => W n

@[simp ↓, expose, implicit_reducible]
def myHint {α : Sort u} {β : Sort v} {γ : Sort w} (_v : α) (_binder : β) (e : γ) : γ := e

-- The marker unfolds first: constant time, within a small heartbeat budget.
set_option maxHeartbeats 400 in
example : binderNameHint 0 (fun n : Nat => n) (W 100000) = W 100000 := rfl

-- A regular definition in marker position unfolds after the payload: the comparison reduces
-- `W 100000` and exceeds the default recursion depth.
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : myHint 0 (fun n : Nat => n) (W 100000) = W 100000 := rfl
