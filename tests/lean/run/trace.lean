import Init.Lean.Util.Trace
open Lean

structure MyState :=
(traceState : TraceState := {})
(s          : Nat := 0)

abbrev M := ReaderT Options (EStateM String MyState)

/- We can enable tracing for a monad M by adding an instance of `SimpleMonadTracerAdapter M` -/
instance : SimpleMonadTracerAdapter M :=
{ getOptions       := read,
  getTraceState    := MyState.traceState <$> get,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

def tst1 : M Unit :=
do trace! `module ("hello" ++ MessageData.nest 9 (Format.line ++ "world"));
   trace! `module.aux "another message";
   pure ()

def tst2 (b : Bool) : M Unit :=
traceCtx `module $ do
  tst1;
  trace! `bughunt "at test2";
  when b $ throw "error";
  tst1;
  pure ()

partial def ack : Nat → Nat → Nat
| 0,   n   => n+1
| m+1, 0   => ack m 1
| m+1, n+1 => ack m (ack (m+1) n)

def slow (b : Bool) : Nat :=
ack 4 (cond b 0 1)

def tst3 (b : Bool) : M Unit :=
do traceCtx `module $ do {
     tst2 b;
     tst1
   };
   trace! `bughunt "at end of tst3";
   -- Messages are computed lazily. The following message will only be computed
   -- if `trace.slow is active.
   trace! `slow ("slow message: " ++ toString (slow b))

def runM (x : M Unit) : IO Unit :=
let opts := Options.empty;
-- Try commeting/uncommeting the following `setBool`s
let opts := opts.setBool `trace.module true;
-- let opts := opts.setBool `trace.module.aux false;
let opts := opts.setBool `trace.bughunt true;
-- let opts := opts.setBool `trace.slow true;
match x.run opts {} with
| EStateM.Result.ok _ s    => IO.println s.traceState
| EStateM.Result.error _ s => do IO.println "Error"; IO.println s.traceState

def main : IO Unit :=
do IO.println "----";
   runM (tst3 true);
   IO.println "----";
   runM (tst3 false);
   pure ()

#eval main
