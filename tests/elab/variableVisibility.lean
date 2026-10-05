module

/-!
Tests `private`/`public` modifiers on `variable` and the visibility tracking of section variables in
the module system (#10760, #14718, #15302).
-/

structure PrivT where
  n : Nat

public structure PubT where
  n : Nat

/-! Private variables cannot become parameters of public declarations. -/

section
private variable (p : PrivT) (q : PubT)

/-- info: p : PrivT -/
#guard_msgs in
#check p

-- private variables may be used by private declarations
def privUse := p.n + q.n

-- ... and are harmless for public declarations that do not use them
public def unrelated (n : Nat) := n

/--
error: Private section variable `p` cannot be a parameter of the public declaration `usesPriv`

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public def usesPriv := p

-- also applies to variables that are not private for technical reasons
/--
error: Private section variable `q` cannot be a parameter of the public declaration `usesPriv'`

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public def usesPriv' := q

/--
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
---
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public theorem usesPrivThm : p = p := rfl

public variable (r : PubT)

public def usesPub := r.n
public theorem usesPubThm : r = r := rfl
def usesPubPriv := r.n + p.n

/-- info: usesPub : PubT → Nat -/
#guard_msgs in
#with_exporting #check @usesPub

include p in
/--
error: Private section variable `p` cannot be a parameter of the public declaration `inclPriv`

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public theorem inclPriv : True := trivial

include p in
theorem inclPriv' : True := by cases p; trivial
end

/-! Public variables are elaborated in the public scope. -/

section
/--
error: Unknown identifier `PrivT`

Note: A private declaration `PrivT` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
public variable (x : PrivT)
end

public section
/--
error: Unknown identifier `PrivT`

Note: A private declaration `PrivT` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
variable (x : PrivT)

private variable (x : PrivT)

/-- info: x : PrivT -/
#guard_msgs in
#check x

private def privInPublicSection := x

/--
error: Private section variable `x` cannot be a parameter of the public declaration `pubInPublicSection`

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
def pubInPublicSection := x

variable (y : PubT)
def usesPubVar := y
private def usesPubVar' := y.n + x.n
end

/-! Private instance variables are not automatically included in public theorems. -/

section
public variable {β : Type}
private variable [Inhabited β]

public theorem noPrivInst (b : β) : b = b := rfl
theorem privInst (b : β) : b = b := rfl

/-- info: @noPrivInst : ∀ {β : Type} (b : β), b = b -/
#guard_msgs in
#check @noPrivInst

/-- info: @privInst : ∀ {β : Type} [Inhabited β] (b : β), b = b -/
#guard_msgs in
#check @privInst

/--
error: Private section variable `[Inhabited β]` cannot be a parameter of the public declaration `usesPrivInst`

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public def usesPrivInst : β := default

public variable [Inhabited β]
public theorem pubInst (b : β) : b = default → True := fun _ => trivial
public def usesPubInst : β := default
end

/-! Public variables may not depend on private ones. -/

section
private variable (n : Nat)
/--
error: Private section variable `n` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
---
error: Private section variable `n` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public variable (h : n = n)

-- dependency not introduced by a reference
/-- error: Public section variable `h'` cannot depend on the private section variable `n` -/
#guard_msgs in
public variable (h' : ‹Nat› = 0)
end

/-! Binder annotation updates preserve the visibility but may not change it. -/

section
public variable {α : Type}
variable {γ : Type}
variable (α)
public def explicitArg (a : α) := a

/-- info: explicitArg : (α : Type) → α → α -/
#guard_msgs in
#check @explicitArg

/-- error: Cannot change the visibility of the section variable `α` in a binder annotation update -/
#guard_msgs in
private variable {α}

/-- error: Cannot change the visibility of the section variable `γ` in a binder annotation update -/
#guard_msgs in
public variable (γ)

private variable (γ)
def explicitArg' (c : γ) := c
end

/-! Other kinds of declarations. -/

section
private variable (p : PrivT)

/--
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
---
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public inductive Ind where
  | mk (h : p = p)

/--
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
---
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public structure Struct where
  h : p = p

/--
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
---
error: Private section variable `p` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public axiom ax : p = p

/--
error: Private section variable `p` cannot be a parameter of the public declaration `mutA`

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
mutual
public def mutA : Nat → Nat
  | 0 => 0
  | n+1 => mutB n
def mutB : Nat → Nat
  | 0 => p.n
  | n+1 => mutA n
end

inductive Ind' where
  | mk (h : p = p)
structure Struct' where
  h : p = p
axiom ax' : p = p
end

/-! Variables without a modifier default to the visibility of the enclosing section. -/

section
variable (p : PubT) {α : Type} [Inhabited α]

/--
error: Private section variable `p` cannot be a parameter of the public declaration `defaultPriv`

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public def defaultPriv := p.n

/--
error: Private section variable `α` cannot be referenced in the public scope

Hint: Use `public variable` to make a section variable available to public declarations.
-/
#guard_msgs in
public theorem defaultPrivThm (a : α) : a = a := rfl

-- elaborated in the private scope
variable (x : PrivT)
def defaultPrivUse := x.n + p.n
end

public section
variable (p : PubT)
def defaultPub := p.n
end

/-! #14718: private variables can be used by private declarations inside `public section`. -/

public section
private def A := Bool
private def l (s : A) : A := s

private variable (s : A)
private theorem l_eq : l s = s := rfl

/-- info: l_eq (s : A) : l s = s -/
#guard_msgs in
#check l_eq
end

/-! #15302: anonymous public instances are created in the presence of unrelated private variables. -/

section
public class Cls (α : Type) where
class PrivCls where

variable [PrivCls]

public instance : Cls PubT := {}

/-- info: instClsPubT : Cls PubT -/
#guard_msgs in
#check instClsPubT
end
