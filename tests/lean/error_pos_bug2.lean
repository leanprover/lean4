inductive fibrant [class] (T : Type) : Type :=
mk : fibrant T

inductive Fib : Type :=
mk : ΠA : Type, fibrant A → Fib

namespace Fib

definition type [coercion] (F : Fib) : Type := Fib.rec_on F (λA f, A)

definition is_fibrant [instance] (F : Fib) : fibrant (type F) := Fib.rec_on F (λA f, f)

end Fib
-- open Fib
-- Path

inductive path {A : Fib} (a : A) : A → Type :=
idpath : path a a
