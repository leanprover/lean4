/-!
Concurrent first lookups in the interpreter's global native-symbol cache. Every task runs on its
own thread and so gets a fresh interpreter instance; the target functions are first called only
after all tasks have passed the gate, so their global cache entries are created concurrently.
Interpreted functions cache a null native address, the core functions a real one; the results are
compared with a sequential run afterwards. The `task_` prefix puts the test in the subset that the
ThreadSanitizer CI job runs, which is where it is meaningful.
-/

-- Interpreted targets; `noinline` keeps every call a symbol lookup.
@[noinline] def f1 (n : Nat) : Nat := n * 3 + 1 % (n + 1)
@[noinline] def f2 (n : Nat) : Nat := n * 5 + 2 % (n + 2)
@[noinline] def f3 (n : Nat) : Nat := n * 7 + 3 % (n + 3)
@[noinline] def f4 (n : Nat) : Nat := n * 9 + 4 % (n + 4)
@[noinline] def f5 (n : Nat) : Nat := n * 11 + 5 % (n + 5)
@[noinline] def f6 (n : Nat) : Nat := n * 13 + 6 % (n + 6)
@[noinline] def f7 (n : Nat) : Nat := n * 15 + 7 % (n + 7)
@[noinline] def f8 (n : Nat) : Nat := n * 17 + 8 % (n + 8)
@[noinline] def f9 (n : Nat) : Nat := n * 19 + 9 % (n + 9)
@[noinline] def f10 (n : Nat) : Nat := n * 21 + 10 % (n + 10)
@[noinline] def f11 (n : Nat) : Nat := n * 23 + 11 % (n + 11)
@[noinline] def f12 (n : Nat) : Nat := n * 25 + 12 % (n + 12)
@[noinline] def f13 (n : Nat) : Nat := n * 27 + 13 % (n + 13)
@[noinline] def f14 (n : Nat) : Nat := n * 29 + 14 % (n + 14)
@[noinline] def f15 (n : Nat) : Nat := n * 31 + 15 % (n + 15)
@[noinline] def f16 (n : Nat) : Nat := n * 33 + 16 % (n + 16)
@[noinline] def f17 (n : Nat) : Nat := n * 35 + 17 % (n + 17)
@[noinline] def f18 (n : Nat) : Nat := n * 37 + 18 % (n + 18)
@[noinline] def f19 (n : Nat) : Nat := n * 39 + 19 % (n + 19)
@[noinline] def f20 (n : Nat) : Nat := n * 41 + 20 % (n + 20)
@[noinline] def f21 (n : Nat) : Nat := n * 43 + 21 % (n + 21)
@[noinline] def f22 (n : Nat) : Nat := n * 45 + 22 % (n + 22)
@[noinline] def f23 (n : Nat) : Nat := n * 47 + 23 % (n + 23)
@[noinline] def f24 (n : Nat) : Nat := n * 49 + 24 % (n + 24)

@[noinline] def mix (i : Nat) : Nat :=
  let interpreted :=
    f1 (i + 1) + f2 (i + 2) + f3 (i + 3) + f4 (i + 4) +
    f5 (i + 5) + f6 (i + 6) + f7 (i + 7) + f8 (i + 8) +
    f9 (i + 9) + f10 (i + 10) + f11 (i + 11) + f12 (i + 12) +
    f13 (i + 13) + f14 (i + 14) + f15 (i + 15) + f16 (i + 16) +
    f17 (i + 17) + f18 (i + 18) + f19 (i + 19) + f20 (i + 20) +
    f21 (i + 21) + f22 (i + 22) + f23 (i + 23) + f24 (i + 24)
  -- core functions with native code
  let native := (Nat.repr i).length + (List.replicate (i % 7) i).foldl (· + ·) 0
    + (toString i ++ "x").length + (Array.range i).size
  interpreted + native

def main : IO Unit := do
  let numTasks := 32
  let prom ← IO.Promise.new
  let gate := prom.result!
  let tasks ← (List.range numTasks).mapM fun i => IO.asTask (prio := .dedicated) do
    IO.wait gate
    return mix i
  prom.resolve ()
  let results ← tasks.mapM fun t => do IO.ofExcept (← IO.wait t)
  let expected := (List.range numTasks).map mix
  if results == expected then
    IO.println "ok"
  else
    IO.println s!"mismatch: {results} vs {expected}"

#eval main
