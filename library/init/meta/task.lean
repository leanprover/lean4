prelude
import init.data.string.basic init.monad

meta constant {u} task : Type u → Type (max u 1)

namespace task

meta constant {u} get {α : Type u} (t : task α) : α
meta constant {u} pure {α : Type u} (t : α) : task α

end task
