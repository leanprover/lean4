import Lean.Meta

/-!
Tests `Environment.realizationEnvContains`, which reports whether `realizeConst forConst` callbacks
can access a second constant `c`. The realization environment of a local constant contains the
imported constants and all declarations added before its realizations were enabled, which includes
asynchronously elaborated theorems and the other declarations of its mutual block. The realization
environment of an imported constant contains the imported constants only.
-/

open Lean Meta

def a := True
theorem t : True := trivial
def b := True

mutual
def f : Nat → Nat
  | 0 => 0
  | n+1 => g n
def g : Nat → Nat
  | 0 => 0
  | n+1 => f n
end

mutual
def p : Nat → Nat
  | 0 => 0
  | n+1 => q n
termination_by n => n
def q : Nat → Nat
  | 0 => 0
  | n+1 => p n
termination_by n => n
end

def check (forConst c : Name) : MetaM Unit := do
  logInfo m!"{forConst} sees {c}: {(← getEnv).realizationEnvContains forConst c}"

/--
info: b sees a: true
---
info: a sees b: false
---
info: a sees Nat.add: true
---
info: Nat.add sees a: false
---
info: Nat.zero sees Nat.add: true
---
info: b sees t: true
---
info: a sees t: false
---
info: t sees b: false
---
info: f sees g: true
---
info: g sees f: true
---
info: p sees q: true
---
info: q sees p: true
---
info: nonexistent sees a: false
---
info: a sees nonexistent: false
-/
#guard_msgs in
run_meta do
  check ``b ``a
  check ``a ``b
  check ``a ``Nat.add
  check ``Nat.add ``a
  check ``Nat.zero ``Nat.add
  check ``b ``t
  check ``a ``t
  check ``t ``b
  -- structural recursion
  check ``f ``g
  check ``g ``f
  -- well-founded recursion
  check ``p ``q
  check ``q ``p
  check `nonexistent ``a
  check ``a `nonexistent

-- NOTE: declaring and running a `realizeConst` invocation isn't usually done in the same file, so
-- changing the closures below may require a server restart to see the changes.

/-- Realizes `name` for `forConst` with a callback that needs `a`, `b`, and `t`. -/
def realizeBoth (forConst name : Name) : MetaM Unit :=
  realizeConst forConst name do
    let _ ← getConstInfo ``a
    let _ ← getConstInfo ``b
    let _ ← getConstInfo ``t
    addDecl <| .thmDecl {
      name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }

-- `b` is not part of `a`'s realization environment
/-- error: Unknown constant `b` -/
#guard_msgs in
run_meta realizeBoth ``a `a.both

#guard_msgs in
run_meta realizeBoth ``b `b.both

/-- info: b.both : True -/
#guard_msgs in
#check b.both

/-- Realizes `name` for `forConst` with a callback that realizes a constant for `other`. -/
def realizeNested (forConst other name : Name) : MetaM Unit :=
  realizeConst forConst name do
    realizeConst other (name ++ `inner) do
      addDecl <| .thmDecl {
        name := name ++ `inner, levelParams := [], type := mkConst ``True,
        value := mkConst ``True.intro }
    addDecl <| .thmDecl {
      name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }

-- realizations for `b` are not enabled in `a`'s realization environment
/-- info: realization failed -/
#guard_msgs in
run_meta do
  try
    realizeNested ``a ``b `a.nested
    logInfo "realization succeeded"
  catch _ =>
    logInfo "realization failed"

#guard_msgs in
run_meta realizeNested ``b ``a `b.nested

/-- info: b.nested.inner : True -/
#guard_msgs in
#check b.nested.inner
