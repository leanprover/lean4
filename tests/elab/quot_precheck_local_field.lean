/-!
Tests that the quotation precheck accepts field notation on variables bound in the quotation, like
`x.succ` for a bound `x`, including when the precheck expands a macro that binds the variable.
-/

def n := 1

#guard_msgs in
macro "direct" : term => ``(fun (x : Nat) => x.succ)

example : direct 1 = 2 := rfl

#guard_msgs in
macro "nested" : term => ``(fun (x : List Nat) => x.head!.succ)

#guard_msgs in
macro "matchVar" : term => ``(fun (p : Nat × Nat) => match p with | (a, _) => a.succ)

syntax "withSucc " term:max : term
macro_rules | `(withSucc $y) => `(fun (x : Nat) => x.succ + $y)

#guard_msgs in
macro "viaMacro" : term => ``(withSucc n)

example : viaMacro 1 = 3 := rfl

syntax "withId " term:max : term
macro_rules | `(withId $y) => `(fun (x : Nat) => x + $y)

#guard_msgs in
macro "viaMacroPlain" : term => ``(withId n)

-- Unbound identifiers are still rejected, also when a bound variable's name is a string prefix.
/--
error: Unknown identifier `y.succ` at quotation precheck

Note: You can use `set_option quotPrecheck false` to disable this check.
-/
#guard_msgs in
macro "unbound" : term => ``(fun (x : Nat) => y.succ)

/--
error: Unknown identifier `xy.succ` at quotation precheck

Note: You can use `set_option quotPrecheck false` to disable this check.
-/
#guard_msgs in
macro "stringPrefix" : term => ``(fun (x : Nat) => xy.succ)
