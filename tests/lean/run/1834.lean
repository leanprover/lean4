/-!
# Pretty print with `∀` instead of `→` when domain is type

https://github.com/leanprover/lean4/issues/1834
-/

set_option linter.unusedVariables false

/-!
Tests of various pi types.
-/
section
variable (α : Nat → Type) (p q : Prop) (P : Nat → Prop)

-- default nondep
/-- info: Nat → Nat : Type -/
#guard_msgs in #check (i : Nat) → Nat
-- implicit nondep
/-- info: {i : Nat} → Nat : Type -/
#guard_msgs in #check {i : Nat} → Nat
-- instance implicit nondep
/-- info: [Inhabited Nat] → Nat : Type -/
#guard_msgs in #check [Inhabited Nat] → Nat
-- default nondep, both prop
/-- info: p → q : Prop -/
#guard_msgs in #check (h : p) → q
-- default nondep, only codomain prop
/-- info: ∀ (i : Nat), p : Prop -/
#guard_msgs in #check (i : Nat) → p
-- implicit nondep, only codomain prop
/-- info: ∀ {i : Nat}, p : Prop -/
#guard_msgs in #check {i : Nat} → p
-- instance implicit nondep, only codomain prop, hygienic name
/-- info: ∀ [Inhabited Nat], p : Prop -/
#guard_msgs in #check [Inhabited Nat] → p
-- instance implicit nondep, only codomain prop, user-provided name
/-- info: ∀ [instNat : Inhabited Nat], p : Prop -/
#guard_msgs in #check [instNat : Inhabited Nat] → p
-- default dep
/-- info: (i : Nat) → α i : Type -/
#guard_msgs in #check (i : Nat) → α i
-- implicit dep
/-- info: {i : Nat} → α i : Type -/
#guard_msgs in #check {i : Nat} → α i
-- instance implicit dep
/-- info: [inst : Inhabited Nat] → α default : Type -/
#guard_msgs in #check [Inhabited Nat] → α default
-- default dep, codomain prop
/-- info: ∀ (i : Nat), P i : Prop -/
#guard_msgs in #check (i : Nat) → P i
-- implicit dep, codomain prop
/-- info: ∀ {i : Nat}, P i : Prop -/
#guard_msgs in #check {i : Nat} → P i
-- instance implicit dep, codomain prop, hygienic name
/-- info: ∀ [inst : Inhabited Nat], P default : Prop -/
#guard_msgs in #check [Inhabited Nat] → P default
-- instance implicit dep, codomain prop, user-provided name
/-- info: ∀ [instNat : Inhabited Nat], P default : Prop -/
#guard_msgs in #check [instNat : Inhabited Nat] → P default

-- Same tests but with `pp.foralls` set to false.
set_option pp.foralls false

-- default nondep
/-- info: Nat → Nat : Type -/
#guard_msgs in #check (i : Nat) → Nat
-- implicit nondep
/-- info: {i : Nat} → Nat : Type -/
#guard_msgs in #check {i : Nat} → Nat
-- default nondep, both prop
/-- info: p → q : Prop -/
#guard_msgs in #check (h : p) → q
-- default nondep, only codomain prop
/-- info: Nat → p : Prop -/
#guard_msgs in #check (i : Nat) → p
-- default dep
/-- info: (i : Nat) → α i : Type -/
#guard_msgs in #check (i : Nat) → α i
-- implicit dep
/-- info: {i : Nat} → α i : Type -/
#guard_msgs in #check {i : Nat} → α i
-- default dep, codomain prop
/-- info: (i : Nat) → P i : Prop -/
#guard_msgs in #check (i : Nat) → P i
-- implicit dep, codomain prop
/-- info: {i : Nat} → P i : Prop -/
#guard_msgs in #check {i : Nat} → P i
-- implicit nondep, only codomain prop
/-- info: {i : Nat} → p : Prop -/
#guard_msgs in #check {i : Nat} → p
end

/-!
Rewrote forall, remains a forall, since domain is `Nat`.
-/
/--
info: P : Nat → Prop
q : Prop
h : ∀ (n : Nat), P n = q
hq : q
⊢ ∀ (n : Nat), q
-/
#guard_msgs in
example (P : Nat → Prop) (q : Prop) (h : ∀ n, P n = q) (hq : q) :
    ∀ n, P n := by
  conv => enter [n]; rw [h]
  trace_state
  exact fun _ => hq

/-!
When `pp.foralls` is false, uses non-dependent `→`.
-/
/--
info: P : Nat → Prop
q : Prop
h : (n : Nat) → P n = q
hq : q
⊢ Nat → q
-/
#guard_msgs in
set_option pp.foralls false in
example (P : Nat → Prop) (q : Prop) (h : ∀ n, P n = q) (hq : q) :
    ∀ n, P n := by
  conv => enter [n]; rw [h]
  trace_state
  exact fun _ => hq

/-!
Rewrote forall, turns into an implication, since domain is a proposition.
-/
/--
info: p : Prop
P : p → Prop
q : Prop
h : ∀ (n : p), P n = q
hq : q
⊢ p → q
-/
#guard_msgs in
example (p : Prop) (P : p → Prop) (q : Prop) (h : ∀ n, P n = q) (hq : q) :
    ∀ n, P n := by
  conv => enter [n]; rw [h]
  trace_state
  exact fun _ => hq
