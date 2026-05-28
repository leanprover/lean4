/-!
# `backward.inferDefEqOnRfl` and `backward.inferDefEqOnRfl.trace`

`backward.inferDefEqOnRfl` is an adaption helper: it makes `:= rfl` theorems
auto-tagged `[defeq]` (when the strict instance-transparency check passes) or
`[backward_defeq]` (otherwise), instead of the post-migration default of always
tagging `[backward_defeq]`.

`backward.inferDefEqOnRfl.trace` additionally logs an info message for each
theorem inferred as `[defeq]`.
-/

@[implicit_reducible] def fast (n : Nat) : Nat := n
def slow (n : Nat) : Nat := n + 0

-- Default: `:= rfl` is tagged `[backward_defeq]` only, no info messages.
theorem fast_eq_default (n : Nat) : fast n = n := rfl
theorem slow_eq_default (n : Nat) : slow n = n := rfl

/-- info: @[backward_defeq] theorem fast_eq_default : ∀ (n : Nat), fast n = n -/
#guard_msgs in
#print sig fast_eq_default

/-- info: @[backward_defeq] theorem slow_eq_default : ∀ (n : Nat), slow n = n -/
#guard_msgs in
#print sig slow_eq_default

-- With `backward.inferDefEqOnRfl`, `fast_eq` (passes strict) gets `[defeq]`,
-- `slow_eq` (only default-transparency-defeq) gets `[backward_defeq]`.
-- No info messages because the trace option is not set.
set_option backward.inferDefEqOnRfl true in
theorem fast_eq_silent (n : Nat) : fast n = n := rfl

set_option backward.inferDefEqOnRfl true in
theorem slow_eq_silent (n : Nat) : slow n = n := rfl

/-- info: @[defeq] theorem fast_eq_silent : ∀ (n : Nat), fast n = n -/
#guard_msgs in
#print sig fast_eq_silent

/-- info: @[backward_defeq] theorem slow_eq_silent : ∀ (n : Nat), slow n = n -/
#guard_msgs in
#print sig slow_eq_silent

-- With `backward.inferDefEqOnRfl.trace` set in addition, an info message is
-- logged when `[defeq]` is inferred, but not when only `[backward_defeq]` is.
set_option backward.inferDefEqOnRfl true in
set_option backward.inferDefEqOnRfl.trace true in
/-- info: `:= rfl` theorem `fast_eq_traced`: inferred @[defeq] -/
#guard_msgs in
theorem fast_eq_traced (n : Nat) : fast n = n := rfl

set_option backward.inferDefEqOnRfl true in
set_option backward.inferDefEqOnRfl.trace true in
#guard_msgs in
theorem slow_eq_traced (n : Nat) : slow n = n := rfl

-- With *only* the trace option (without the main option), nothing happens.
set_option backward.inferDefEqOnRfl.trace true in
theorem fast_eq_trace_only (n : Nat) : fast n = n := rfl

/-- info: @[backward_defeq] theorem fast_eq_trace_only : ∀ (n : Nat), fast n = n -/
#guard_msgs in
#print sig fast_eq_trace_only
