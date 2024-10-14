import Lean.CoreM

open Lean

structure MyState :=
(trace_state : TraceState := {})
(s          : Nat := 0)

abbrev M := CoreM

def tst1 : M Unit :=
do trace[module] (m!"hello" ++ MessageData.nest 9 (m!"\n" ++ "world"));
   trace[module.aux] "another message";
   pure ()

def tst2 (b : Bool) : M Unit :=
withTraceNode `module (fun _ => return "message") do
  tst1;
  trace[bughunt] "at test2";
  if b then throwError "error";
  tst1;
  pure ()

partial def ack : Nat → Nat → Nat
| 0,   n   => n+1
| m+1, 0   => ack m 1
| m+1, n+1 => ack m (ack (m+1) n)

def slow (b : Bool) : Nat :=
ack 4 (cond b 0 1)

def tst3 (b : Bool) : M Unit :=
do withTraceNode `module.slow (fun _ => return m!"slow: {slow b}") do {
     tst2 b;
     tst1
   };
   trace[bughunt] "at end of tst3";
   -- Messages are computed lazily. The following message will only be computed
   -- if `trace.slow is active.
   trace[slow] (m!"slow message: " ++ toString (slow b))
   -- This is true even if it is a monad computation:
   trace[slow] (m!"slow message: " ++ (← pure (toString (slow b))))

def run (x : M Unit) : M Unit :=
withReader
  (fun ctx =>
    -- Try commenting/uncommeting the following `setBool`s
    let opts := ctx.options;
    let opts := opts.setBool `trace.module true;
    -- let opts := opts.setBool `trace.module.aux false;
    let opts := opts.setBool `trace.bughunt true;
    -- let opts := opts.setBool `trace.slow true;
    { ctx with options := opts })
  (tryCatch (tryFinally x printTraces) (fun _ => IO.println "ERROR"))

/--
info: [module] message
  [module] hello
               world
  [bughunt] at test2
ERROR
---
info: [module] message
  [module] hello
               world
  [bughunt] at test2
-/
#guard_msgs in
#eval run (tst3 true)

/--
info: [module] message
  [module] hello
               world
  [bughunt] at test2
  [module] hello world
[module] hello
             world
[bughunt] at end of tst3
---
info: [module] message
  [module] hello
               world
  [bughunt] at test2
  [module] hello
               world
[module] hello
             world
[bughunt] at end of tst3
-/
#guard_msgs in
#eval run (tst3 false)
