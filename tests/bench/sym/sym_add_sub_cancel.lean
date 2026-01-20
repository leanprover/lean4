import Lean

/-!
A Synthetic Benchmark from the Lean@Google Hackathon.
-/

namespace Eval
abbrev Byte := UInt8
abbrev Word := UInt32

def Word.ofInt (a : Int) : Word :=
  UInt32.ofInt a

def Word.add (a b : Option Word) : Word :=
  match a, b with
  | some a, some b => a+b
  | _, _ => 0

def Word.sub (a b : Option Word) : Word :=
  match a, b with
  | some a, some b => a-b
  | _, _ => 0

theorem Word.add_sub_cancel (v : Word) : Word.sub (some (Word.add (some v) (some v))) (some v) = v := by
  simp [Word.add, Word.sub]

theorem Word.add_zero (x : Word) : Word.add (some x) (some (Word.ofInt 0)) = x := by
  simp [Word.add, Word.ofInt, UInt32.ofInt]

structure PartialMap (A B : Type) where
  fn : A -> Option B

def PartialMap.empty (A B : Type) : PartialMap A B :=
  { fn := fun _ => none }

def PartialMap.get {A B : Type} (m : PartialMap A B) (k : A) : Option B :=
  m.fn k

def PartialMap.put [DecidableEq A] (m : PartialMap A B) (k : A) (v : B) : PartialMap A B :=
  { fn := fun x => if x = k then some v else m.fn x }

def PartialMap.remove [DecidableEq A] (m : PartialMap A B) (k : A) : PartialMap A B :=
  { fn := fun x => if x = k then none else m.fn x }

@[ext] theorem PartialMap.ext (m₁ m₂ : PartialMap A B) (h : ∀ k, m₁.get k = m₂.get k) : m₁ = m₂ := by
  cases m₁; cases m₂; congr; funext; apply h

theorem PartialMap.get_put {A B : Type} [DecidableEq A] (m : PartialMap A B) (k : A) (v : B)
    : (m.put k v).get k = some v := by
  simp [PartialMap.get, PartialMap.put]

theorem PartialMap.get_put_diff {A B : Type} [DecidableEq A] (m : PartialMap A B) (k k' : A) (v : B)
    (h : k ≠ k') : (m.put k' v).get k = m.get k :=
  if_neg h

theorem PartialMap.put_put {A B : Type} [DecidableEq A] (m : PartialMap A B) (k : A) (v1 v2 : B)
    : (m.put k v1).put k v2 = m.put k v2 := by
  ext; grind +splitImp [PartialMap.get_put, PartialMap.get_put_diff]

inductive Binop where
  | add | sub
  deriving Repr

def Binop.interp (op : Binop) (a b : Option Word) : Word :=
  match op with
  | .add => Word.add a b
  | .sub => Word.sub a b

theorem Binop.interp_add (w1 w2 : Option Word) : Binop.interp .add w1 w2 = Word.add w1 w2 :=
  rfl

theorem Binop.interp_sub (w1 w2 : Option Word) : Binop.interp .sub w1 w2 = Word.sub w1 w2 :=
  rfl

inductive Expr where
  | literal (v: Int)
  | var (x: String)
  | op (bop : Binop) (e1 e2 : Expr)
  deriving Repr

def Expr.eval (me : PartialMap Word Byte) (le : PartialMap String Word) (e : Expr) : Option Word :=
  match e with
  | .literal v    => some (Word.ofInt v)
  | .var x        => le.get x
  | .op bop e1 e2 => some (bop.interp (e1.eval me le) (e2.eval me le))

inductive Cmd where
  | skip : Cmd
  | set : String → Expr → Cmd
  | unset : String → Cmd
  | cond : Expr → Cmd → Cmd → Cmd
  | seq : Cmd → Cmd → Cmd
  | input : String → Cmd
  | output : String → Cmd
  deriving Repr

inductive IOEvent
  | IN : Word → IOEvent
  | OUT : Word → IOEvent

inductive Exec :
    Cmd → List IOEvent → PartialMap Word Byte → PartialMap String Word →
    (List IOEvent → PartialMap Word Byte → PartialMap String Word → Prop) → Prop
| skip :
    post t m l → Exec .skip t m l post
| seq :
    Exec c1 t m l mid →
    (∀ t' m' l', mid t' m' l' → Exec c2 t' m' l' post) →
    Exec (.seq c1 c2) t m l post
| set :
    Expr.eval m l e = some v →
    post t m (PartialMap.put l x v) →
    Exec (.set x e) t m l post
| input :
    (∀ v, post (IOEvent.IN v :: t) m (PartialMap.put l x v)) →
    Exec (.input x) t m l post

theorem Exec.seq_cps (t : List IOEvent) (c1 c2 : Cmd) (m : PartialMap Word Byte) (l : PartialMap String Word)
    (post : List IOEvent → PartialMap Word Byte → PartialMap String Word → Prop)
    : Exec c1 t m l (λ t' m' l' => Exec c2 t' m' l' post) →
      Exec (.seq c1 c2) t m l post := by
  intro h; apply Exec.seq
  apply h; intros; assumption

/-
Generates a command sequence of the form
```
t := t + t
t := t - x
...
t := t + t
t := t - x
```
-/
def repeated_cmds (n : Nat) (t x : String) : Cmd :=
  match n with
  | 0 => .skip
  | n + 1 =>
    .seq (.set t (.op .add (.var t) (.var t)))
         (.seq (.set t (.op .sub (.var t) (.var x)))
               (repeated_cmds n t x))

/-
Generates a command sequence of the form
```
input x
t := x
t := t + t
t := t - x
...
t := t + t
t := t - x
```
-/
def generated_cmd (n : Nat) (t x : String) : Cmd :=
  .seq (.input x)
       (.seq (.set t (.var x))
             (repeated_cmds n t x))

/--
The correctness specification for `generated_cmd n "a" "b"`.

States that for any initial memory `m` and local environment `l`, executing
the generated command starting with an empty I/O trace results in:
- The memory `m'` remaining unchanged (`m' = m`)
- The I/O trace containing exactly one input event with some value `v`
- The local variable `"a"` holding the input value `v`

The generated command reads input into `"b"`, copies it to `"a"`, then performs
`n` iterations of `a := a + a; a := a - b`. Since `(a + a) - a = a`, each iteration
is a no-op, so `"a"` retains the original input value.
-/
def Goal (n : Nat) : Prop :=
  ∀ m l, Exec (generated_cmd n "a" "b") [] m l fun t' m' l' =>
            m' = m ∧
            ∃ v : Word, t' = [IOEvent.IN v] ∧ l'.get "a" = some v

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Meta Elab Tactic

/-- Helper function for executing a tactic `k` for solving `Goal n`. -/
def driver (n : Nat) (check := true) (k : MVarId → MetaM Unit) : MetaM Unit := do
  let some goal ← unfoldDefinition? (mkApp (mkConst ``Goal) (mkNatLit n)) | throwError "UNFOLD FAILED!"
  let mvar ← mkFreshExprMVar goal
  let startTime ← IO.monoNanosNow
  k mvar.mvarId!
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  if check then
    let startTime ← IO.monoNanosNow
    checkWithKernel (← instantiateExprMVars mvar)
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"goal_{n}: {ms} ms, kernel: {kernelMs} ms"
  else
    IO.println s!"goal_{n}: {ms} ms"

/-!
`MetaM` Solution
-/

/-
A tactic for solving goal `Goal n`
-/
macro "solve" : tactic => `(tactic| {
  intros m l;
  simp only [generated_cmd, repeated_cmds];
  apply Exec.seq_cps;
  apply Exec.input;
  intros v;
  repeat (
    apply Exec.seq_cps;
    apply Exec.set;
    simp only [Expr.eval];
    simp only [PartialMap.get_put_diff, PartialMap.get_put, PartialMap.put_put, Binop.interp_add,
          Binop.interp_sub, Word.add_sub_cancel, Option.some.injEq, not_false_eq_true, String.reduceEq, ne_eq];
    try rfl);
  apply Exec.skip;
  simp only [List.cons.injEq, IOEvent.IN.injEq, and_true, PartialMap.put_put, PartialMap.get_put,
    Option.some.injEq, and_self, exists_eq']
})

/--
Solves a goal of the form `Goal n` using the `solve` tactic.
-/
def solveUsingMeta (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => do
    let ([], _) ← runTactic mvarId (← `(tactic| solve)).raw {} {} | throwError "FAILED!"

def runBenchUsingMeta : MetaM Unit := do
  IO.println "=== Symbolic Simulation Tests ==="
  IO.println ""
  for n in [10, 20, 30, 40, 50, 60, 70, 80] do
    solveUsingMeta n

#eval runBenchUsingMeta
