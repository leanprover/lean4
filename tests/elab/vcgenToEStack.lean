import Std.Tactic.Do
import Std.WP

/-!
`vcgen` weakens a concrete exception postcondition of a spec with pointwise verification
conditions: for a bare `ε → Prop` such as the one of `Except ε`, and for a type such as `Thrown`
that converts to a stack via `ToEStack`. A schematic component is assigned the goal's component.
A `throws` clause of a `def` contract fills `Thrown` via its `EPostSlot` instance.
-/

set_option experimental.vcgen true
set_option experimental.intrinsic true
open Std.WP Lean.Order

/-! ## A bare `ε → Prop` -/

def fails : Except String Nat := .error "x"

@[spec] theorem fails_spec : ⦃True⦄ fails ⦃fun _ => False; fun e => e = "x"⦄ :=
  ⟨fun _ => rfl⟩

/--
trace: case vc1
a✝¹ : String
a✝ : a✝¹ = "x"
⊢ a✝¹ = "x" ∨ a✝¹ = "y"
-/
#guard_msgs in
example : ⦃True⦄ fails ⦃fun _ => False; fun e => e = "x" ∨ e = "y"⦄ := by
  vcgen
  trace_state
  grind

/-! ## A type with a `ToEStack` instance -/

/-- The exception postcondition of a `Prog`: what holds of the thrown message. -/
structure Thrown where
  /-- The assertion about the thrown message. -/
  onThrow : String → Prop

instance : PartialOrder Thrown where
  rel p q := p.onThrow ⊑ q.onThrow
  rel_refl := PartialOrder.rel_refl
  rel_trans h₁ h₂ := PartialOrder.rel_trans h₁ h₂
  rel_antisymm h₁ h₂ := congrArg Thrown.mk (PartialOrder.rel_antisymm h₁ h₂)

instance : CompleteLattice Thrown where
  has_sup c :=
    let ⟨sup, hsup⟩ := CompleteLattice.has_sup (fun f => c ⟨f⟩)
    ⟨⟨sup⟩, fun q =>
      ⟨fun hq p hp => (hsup q.onThrow).mp hq p.onThrow hp,
       fun h => (hsup q.onThrow).mpr fun f hf => h ⟨f⟩ hf⟩⟩

instance : ToEStack Thrown EStack⟨String → Prop⟩ where
  toEStack t := estack⟨t.onThrow⟩
  le_of_toEStack_le h := h.1

/-- A program that returns or throws a message. -/
inductive Prog (α : Type) where
  | ret (a : α)
  | throw (e : String)

instance : WP (Prog α) α Prop Thrown where
  trans
    | .ret a => ⟨fun post _ => post a⟩
    | .throw e => ⟨fun _ epost => epost.onThrow e⟩
  trans_monotone
    | .ret _ => fun _ _ _ _ _ hpost => hpost _
    | .throw e => fun _ _ _ _ hepost _ => hepost e

axiom Q : String → Prop

def boom : Prog Unit := .throw "boom"

def boom' : Prog Unit := .throw "boom"

@[spec] theorem boom_spec {post : Unit → Prop} :
    ⦃True⦄ boom ⦃post; { onThrow e := e = "boom" }⦄ := ⟨fun _ => rfl⟩

@[spec] theorem boom'_spec {post : Unit → Prop} {E : String → Prop} :
    ⦃E "boom"⦄ boom' ⦃post; { onThrow := E }⦄ := ⟨PartialOrder.rel_refl⟩

/--
trace: case vc1
a✝¹ : String
a✝ : a✝¹ = "boom"
⊢ a✝¹ = "boom" ∨ a✝¹ = "crash"
-/
#guard_msgs in
example : ⦃True⦄ boom ⦃fun _ => True; { onThrow e := e = "boom" ∨ e = "crash" }⦄ := by
  vcgen
  trace_state
  grind

example : ⦃Q "boom"⦄ boom' ⦃fun _ => True; { onThrow := Q }⦄ := by
  vcgen

def isBoom (e : String) : Prop := e = "boom"

def boom'' : Prog Unit := .throw "boom"

@[spec] theorem boom''_spec {post : Unit → Prop} :
    ⦃True⦄ boom'' ⦃post; { onThrow := isBoom }⦄ := ⟨fun _ => rfl⟩

-- A named assertion stays folded in the verification condition.
/--
trace: case vc1
a✝¹ : String
a✝ : isBoom a✝¹
⊢ isBoom a✝¹ ∨ a✝¹ = "crash"
-/
#guard_msgs in
example : ⦃True⦄ boom'' ⦃fun _ => True; { onThrow e := isBoom e ∨ e = "crash" }⦄ := by
  vcgen
  trace_state
  grind

/-! ## `throws` clauses on `Thrown` -/

instance : EPostSlot Thrown String Prop where
  set R _ := { onThrow := R }

@[spec] theorem Prog.ret_spec {a : α} {post : α → Prop} {E : Thrown} :
    ⦃post a⦄ (Prog.ret a) ⦃post; E⦄ := ⟨PartialOrder.rel_refl⟩

@[spec] theorem Prog.throw_spec {e : String} {post : α → Prop} {E : Thrown} :
    ⦃E.onThrow e⦄ (Prog.throw e : Prog α) ⦃post; E⦄ := ⟨PartialOrder.rel_refl⟩

def okC : Prog Unit ensures _ => True := .ret ()

def boomC : Prog Unit ensures _ => True throws e => e = "boom" := .throw "boom"

/-- info: okC.spec : ⦃ ⊤ ⦄ okC ⦃ fun x => True ⦄ -/
#guard_msgs in #check okC.spec

/-- info: boomC.spec : ⦃ ⊤ ⦄ boomC ⦃ fun x => True; { onThrow := fun e => e = "boom" } ⦄ -/
#guard_msgs in #check boomC.spec

example : ⦃True⦄ boomC ⦃fun _ => True; { onThrow e := e = "boom" ∨ e = "x" }⦄ := by
  vcgen
  grind
