import Lean

example 
  : (fun x : Nat => x + 0)
    =
    fun x => x
  := 
by
  trace_state
  set_option pp.funBinderTypes true in
  trace_state; trace_state
  trace_state

  set_option pp.funBinderTypes false in

  conv => 
    trace_state
    set_option pp.funBinderTypes true in
    trace_state; trace_state
    trace_state

