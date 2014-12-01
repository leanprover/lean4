import data.unit
open unit
namespace play
constant int : Type.{1}
constant nat : Type.{1}
constant izero : int
constant nzero : nat
constant isucc : int → int
constant nsucc : nat → nat
definition f [coercion] (a : unit) : int := izero
definition g [coercion] (a : unit) : nat := nzero

set_option pp.coercions true
check isucc star
check nsucc star
end play
