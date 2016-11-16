import debugger

set_option debugger true
set_option debugger.autorun true

open tactic

local attribute [breakpoint] tactic.constructor

example (p q : Prop) : p → q → p ∧ q :=
by do intros, constructor, repeat assumption
