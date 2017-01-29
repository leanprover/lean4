prelude
import init.category

meta constant {u} task : Type u → Type u

namespace task

meta constant {u} get {α : Type u} (t : task α) : α
protected meta constant {u} pure {α : Type u} (t : α) : task α
protected meta constant {u v} map {α : Type u} {β : Type v} (f : α → β) (t : task α) : task β
protected meta constant {u} flatten {α : Type u} : task (task α) → task α

protected meta def {u v} bind {α : Type u} {β : Type v} (t : task α) (f : α → task β) : task β :=
task.flatten (task.map f t)

meta instance : monad task :=
{ map := @task.map, bind := @task.bind, ret := @task.pure }

@[inline]
meta def {u} delay {α : Type u} (f : unit → α) : task α :=
task.map f (return ())

end task
