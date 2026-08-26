import Lean

/-!
Regression test for `Environment.getLocalConstantInfos` (lean4#13705).

A child's nested `AsyncConsts` inherit every sibling constant that already existed when its
asynchronous elaboration forked, so a naive recursive walk revisits them (multiplicatively in the
nesting depth). This pins down that `getLocalConstantInfos` deduplicates by name and returns the
constants in elaboration order, and that `skipTheoremSubDecls` controls descent into theorem bodies.

Note the ordering: a `def`'s `where` helper commits as its own top-level constant before its parent,
so `a.ha` precedes `a`; a theorem's helper is only reachable by descending into the theorem body, so
`t.ht` follows `t`.
-/

open Lean

def a : Nat := 0 where ha : Nat := 1
def b : Nat := 0 where hb : Nat := 1
def c : Nat := 0 where hc : Nat := 1

theorem t : True := trivial where
  ht : Nat := 1

/-- info: #[`a.ha, `a, `b.hb, `b, `c.hc, `c, `t, `t.ht] -/
#guard_msgs in
#eval show CoreM (Array Name) from do
  return (← (← getEnv).getLocalConstantInfos).map (·.name)

/-- info: #[`a.ha, `a, `b.hb, `b, `c.hc, `c, `t] -/
#guard_msgs in
#eval show CoreM (Array Name) from do
  return (← (← getEnv).getLocalConstantInfos (skipTheoremSubDecls := true)).map (·.name)
