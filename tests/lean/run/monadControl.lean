@[inline] def f {α} (s : String) (x : IO α) : IO α := do
IO.println "started";
IO.println s;
let a ← x;
IO.println ("ended");
pure a

@[inline] def f'' {α m} [MonadControlT IO m] [Monad m] (msg : String) (x : m α) : m α := do
controlAt IO fun runInBase => f msg (runInBase x)

abbrev M := StateT Bool $ ExceptT String $ StateT String $ ReaderT Nat $ StateT Nat IO

def tst : M Nat := do
let a ← f'' "hello" do {
  let s ← getThe Nat; let ctx ← read; modifyThe Nat fun s => s + ctx; if s > 10 then { throw "ERROR" }; getThe Nat };
modifyThe Nat Nat.succ;
pure a

/--
info: started
hello
ended
---
info: ((Except.error "ERROR", "world"), 1011)
-/
#guard_msgs in
#eval (((tst.run true).run "world").run 1000).run 11

@[inline] def g {α} (s : String) (x : Nat → IO α) : IO α := do
IO.println "started";
IO.println s;
let a ← x s.length;
IO.println ("ended");
pure a

@[inline] def g' {α m} [MonadControlT IO m] [Monad m] (msg : String) (x : Nat → m α) : m α := do
controlAt IO fun runInBase => g msg (fun n => runInBase (x n))

def tst2 : M Nat := do
let a ← g' "hello" fun x => do { let s ← getThe Nat; let ctx ← read; modifyThe Nat fun s => s + ctx + x; if s > 10 then { throw "ERROR" }; getThe Nat };
modifyThe Nat Nat.succ;
pure a

/--
info: started
hello
ended
---
info: ((Except.ok (1015, true), "world"), 1016)
-/
#guard_msgs in
#eval (((tst2.run true).run "world").run 1000).run 10
