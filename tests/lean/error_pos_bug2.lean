inductive fibrant [class] (T : Type) : Type :=
mk : fibrant T

structure Fib : Type :=
(type : Type) (is_fibrant : fibrant type)

namespace Fib

attribute type [coercion]
attribute is_fibrant [instance]

end Fib
-- open Fib
-- Path

inductive path {A : Fib} (a : A) : A → Type :=
idpath : path a a
