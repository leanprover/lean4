namespace X1

mutual inductive foo, bar
with foo : Type
| mk : foo
with bar : Type
| mk : bar

check @foo
check @bar
check @foo.rec
check @bar.rec
check @foo.has_sizeof_inst
check @bar.has_sizeof_inst
end X1

namespace X2

mutual inductive foo, bar
with foo : Type
| mk : bar -> foo
with bar : Type
| mk : foo -> bar

check @foo
check @bar
check @foo.rec
check @bar.rec
check @foo.has_sizeof_inst
check @bar.has_sizeof_inst
end X2

namespace X3

mutual inductive foo, bar
with foo : bool -> Type
| mk : bar -> foo tt
with bar : Type
| mk : foo tt -> bar

check @foo
check @bar
check @foo.rec
check @bar.rec
check @foo.has_sizeof_inst
check @bar.has_sizeof_inst
end X3

namespace X4

mutual inductive foo, bar, rig
with foo : bool -> bool -> Type
| mk : bar tt -> foo tt tt
with bar : bool -> Type
| mk : foo tt tt -> bar tt
with rig : Type
| mk : foo tt tt -> bar tt -> rig

check @foo
check @bar
check @rig
check @foo.rec
check @bar.rec
check @rig.rec
check @foo.has_sizeof_inst
check @bar.has_sizeof_inst
check @rig.has_sizeof_inst
end X4

namespace X5
mutual inductive foo, bar, rig (A : Type)
with foo : Pi (b : bool), b = b -> Type
| mk : A -> bar tt ff tt -> foo tt rfl
with bar : bool -> bool -> bool -> Type
| mk : A -> foo tt rfl -> bar tt ff tt
with rig : Type
| mk : A -> foo tt rfl -> bar tt ff tt -> rig
| put : A -> foo tt rfl -> bar tt ff tt -> rig

check @foo
check @bar
check @rig
check @foo.rec
check @bar.rec
check @rig.rec
check @foo.has_sizeof_inst
check @bar.has_sizeof_inst
check @rig.has_sizeof_inst
end X5

namespace X6

mutual inductive {l₁ l₂} foo, bar, rig (A : Type.{l₁}) (B : Type.{l₂})
with foo : Pi (b : bool), b = b -> Type.{max l₁ l₂}
| mk : A -> B -> bar tt ff tt -> foo tt rfl
with bar : bool -> bool -> bool -> Type.{max l₁ l₂}
| mk : A -> B -> foo tt rfl -> bar tt ff tt
with rig : Type.{max l₁ l₂}
| mk : A -> B -> foo tt rfl -> bar tt ff tt -> rig

check @foo
check @bar
check @rig
check @foo.rec
check @bar.rec
check @rig.rec
end X6

namespace X7

mutual inductive {l₁ l₂ l₃} foo, bar, rig (A : Type.{l₁}) (B : Type.{l₂}) (a : A)
with foo : Pi (b : bool), b = b -> Type.{max l₁ l₂ l₃}
| mk : A -> B -> Pi x : A, x = a -> bar tt ff tt -> foo tt rfl
with bar : bool -> bool -> bool -> Type.{max l₁ l₂ l₃}
| mk : A -> B -> foo tt rfl -> bar tt ff tt
with rig : Type.{max l₁ l₂ l₃}
| mk : A -> B -> (Pi x : A, x = a -> foo tt rfl) -> bar tt ff tt -> rig

check @foo
check @bar
check @rig
check @foo.rec
check @bar.rec
check @rig.rec

end X7
