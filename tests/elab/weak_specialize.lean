module

public section

/-!
This test checks that weak_specialize:
- doesn't trigger specialization on its own
- does get included in specialization if other parameters provoke specialization
- does not affect the semantics of nospecialize parameters
-/

@[weak_specialize] class MyWeak (α : Type) where
  val : α

/-- -/
#guard_msgs in
set_option trace.Compiler.specialize.info true in
def weakOnly [MyWeak α] (x : α) : α := x

class MyStrong (α : Type) where
  op : α → α

/-- trace: [Compiler.specialize.info] weakAndStrong [N, W, I, O] -/
#guard_msgs in
set_option trace.Compiler.specialize.info true in
def weakAndStrong [MyWeak α] [MyStrong α] (x : α) : α := MyStrong.op x

@[nospecialize] class MyNoSpec (α : Type) where
  val : α

/-- trace: [Compiler.specialize.info] nospecAndStrong [N, O, I, O] -/
#guard_msgs in
set_option trace.Compiler.specialize.info true in
def nospecAndStrong [MyNoSpec α] [MyStrong α] (x : α) : α := MyStrong.op x
