import Lean
import UserAttr.BlaAttr

@[bla] def f (x : Nat) := x + 2
@[bla] def g (x : Nat) := x + 1

@[foo 10] def h1 (x : Nat) := 2*x + 1
@[foo 20 important] def h2 (x : Nat) := 2*x + 1

open Lean in
def hasBlaAttr (declName : Name) : CoreM Bool :=
  return blaAttr.hasTag (← getEnv) declName

#eval hasBlaAttr ``f
#eval hasBlaAttr ``id

open Lean in
def getFooAttrInfo? (declName : Name) : CoreM (Option (Nat × Bool)) :=
  return fooAttr.getParam? (← getEnv) declName

#eval getFooAttrInfo? ``f
#eval getFooAttrInfo? ``h1
#eval getFooAttrInfo? ``h2

@[my_simp] theorem f_eq : f x = x + 2 := rfl
@[my_simp] theorem g_eq : g x = x + 1 := rfl

example : f x + g x = 2*x + 3 := by
  fail_if_success simp +arith -- does not apply f_eq and g_eq
  simp +arith [f, g]

example : f x + g x = 2*x + 3 := by
  simp +arith [my_simp]

example : f x = id (x + 2) := by
  simp
  simp [my_simp]

macro "my_simp" : tactic => `(tactic| simp [my_simp])

example : f x = id (x + 2) := by
  my_simp

@[simp low, my_simp low]
axiom expand_mul_add (x y z : Nat) : x * (y + z) = x * y + x * y
@[simp high, my_simp high]
axiom expand_add_mul (x y z : Nat) : (x + y) * z = x * z + y * z
@[simp, my_simp]
axiom lassoc_add (x y z : Nat) : x + (y + z) = x + y + z

set_option trace.Meta.Tactic.simp.rewrite true

-- Rewrites: expand_mul_add -> expand_mul_add -> lassoc_add
theorem ex1 (x : Nat) : (x + x) * (x + x) = x * x + x * x + x * x + x * x := by simp only [my_simp]

-- Rewrites: expand_add_mul -> expand_mul_add -> lassoc_add
theorem ex2 (x : Nat) : (x + x) * (x + x) = x * x + x * x + x * x + x * x := by simp

open Lean Meta in
def checkProofs : MetaM Unit := do
  let .thmInfo info1 ← getConstInfo `ex1 | throwError "unexpected"
  let .thmInfo info2 ← getConstInfo `ex2 | throwError "unexpected"
  unless info1.value == info2.value do
    throwError "unexpected values"

#eval checkProofs

open Lean Meta in
def showThmsOf (simpAttrName : Name) : MetaM Unit := do
  let some simpExt ← getSimpExtension? simpAttrName
    | throwError "`{simpAttrName}` is not a simp attribute"
  let thms ← simpExt.getTheorems
  let thmNames := thms.lemmaNames.fold (init := #[]) fun acc origin => acc.push origin.key
  for thmName in thmNames do
    IO.println thmName

#eval showThmsOf `my_simp

def boo (x : Nat) : Nat :=
  x + 10

open Lean Meta in
simproc [my_simp] reduceBoo (boo _) := fun e => do
  unless e.isAppOfArity ``boo 1 do return .continue
  let some n ← Nat.fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit (n+10) }

example : f x + boo 2 = id (x + 2) + 12 := by
  simp
  simp [my_simp] -- Applies the simp and simproc sets


namespace TraceAdd

set_option trace.Meta.Tactic.simp.rewrite false

/-- info: trace_add attribute added to TraceAdd.foo -/
#guard_msgs in
@[trace_add] def foo := 1

/-- info: trace_add attribute added to TraceAdd.foo -/
#guard_msgs in
attribute [trace_add] foo

/-- info: trace_add attribute added to TraceAdd.structural -/
#guard_msgs in
@[trace_add] def structural : Nat → Nat
  | 0 => 0
  | n+1 => structural n+1
termination_by structural n => n

/-- info: trace_add attribute added to TraceAdd.wf -/
#guard_msgs in
@[trace_add] def wf : Nat → Nat
  | 0 => 0
  | n+1 => wf n+1
termination_by n => n

/--
info: trace_add attribute added to TraceAdd.mutual_structural_1
---
info: trace_add attribute added to TraceAdd.mutual_structural_2
-/
#guard_msgs in
mutual
@[trace_add] def mutual_structural_1 : Nat → Nat
  | 0 => 0
  | n+1 => mutual_structural_2 n+1
termination_by structural n => n
@[trace_add] def mutual_structural_2 : Nat → Nat
  | 0 => 0
  | n+1 => mutual_structural_1 n+1
termination_by structural n => n
end

/--
info: trace_add attribute added to TraceAdd.mutual_wf_1._mutual
---
info: trace_add attribute added to TraceAdd.mutual_wf_1
---
info: trace_add attribute added to TraceAdd.mutual_wf_2
-/
#guard_msgs in
mutual
@[trace_add] def mutual_wf_1 : Nat → Nat
  | 0 => 0
  | n+1 => mutual_wf_2 n+1
termination_by n => n
@[trace_add] def mutual_wf_2 : Nat → Nat
  | 0 => 0
  | n+1 => mutual_wf_1 n+1
termination_by n => n
end

end TraceAdd
