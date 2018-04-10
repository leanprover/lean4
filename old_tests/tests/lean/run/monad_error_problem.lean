namespace issue
universes u v w
class monad_error (ε : out_param $ Type u) (m : Type w → Type v) :=
[monad_m : monad m]
(fail : Π {α : Type w}, ε → m α)

set_option pp.all true

def unreachable {α} {m} [monad_error string m] : m α :=
monad_error.fail m "unreachable"

#check @unreachable
end issue

namespace original_issue
universes u v
class monad_error (ε : out_param $ Type u) (m : Type u → Type v) :=
[monad_m : monad m]
(fail : Π {α : Type u}, ε → m α)

set_option pp.all true

def unreachable {α} {m} [monad_error string m] : m α :=
monad_error.fail m "unreachable"

#check @unreachable
end original_issue
