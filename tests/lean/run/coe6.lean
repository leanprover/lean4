import data.unit
open unit

variable int : Type.{1}
variable nat : Type.{1}
variable izero : int
variable nzero : nat
variable isucc : int → int
variable nsucc : nat → nat
definition f [coercion] (a : unit) : int := izero
definition g [coercion] (a : unit) : nat := nzero

set_option pp.coercions true
check isucc star
check nsucc star
