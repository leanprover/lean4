/-!
# A fallback on a class parameter

The motivating use for a fallback on an implicit binder, from
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Emulating.20eager.20default.20instance.3F
and https://github.com/leanprover-community/iris-lean/pull/576: a class parameter that users almost
never want to write, which should be determined by unification where possible and otherwise take a
section-wide default.

Emulating this with a `@[default_instance]` routes the default through a class goal (`SIdx ?SI`)
that ordinary synthesis attacks and gets stuck on, so the number of aborted searches per
declaration header grows as `k² + 4k` in the number of binders. Attaching the fallback to the class
parameter directly removes the class goal, leaving `6k`.

This file pins the elaboration behaviour, not the counts.
-/

class SIdx (I : Type u) where
  lt : I → I → Prop

class DefaultSI (SI : outParam (Type u)) where
  sidx : SIdx SI

/--
The ambient step-index type, read off the `DefaultSI` instance in scope.

Being reducible this is defeq to the type it names, but it does stay in elaborated types, which
read `OFE (defaultSI Nat ..) α` below rather than `OFE Nat α`. A term elaborator returning the
metavariable that the `outParam` assigned avoids that.
-/
abbrev defaultSI (SI : Type u) [DefaultSI SI] : Type u := SI

/-- `SI` is solved by unification like any implicit argument; the tactic runs only if nothing
determined it. -/
class OFE {SI : Type _ := by exact defaultSI _} [SIdx SI] (α : Type _) where
  Dist : SI → α → α → Prop
  dist_eqv : Equivalence (Dist n)

section
variable {SI : Type _} [instSI : SIdx SI]

-- What a `local stepindex SI` command would expand to.
set_option synthInstance.checkSynthOrder false in
local instance (priority := 10000) instDefaultSI : DefaultSI SI := ⟨instSI⟩

/-- The declaration reported in the thread. Its statement is the same as without the fallback. -/
theorem dist_equivalence [OFE α] {n : SI} : Equivalence (OFE.Dist (α := α) n) :=
  OFE.dist_eqv

/--
info: @dist_equivalence : ∀ {SI : Type u_2} [instSI : SIdx SI] {α : Type u_1} [inst : OFE α] {n : SI},
  Equivalence (OFE.Dist n)
-/
#guard_msgs in
#check @dist_equivalence

-- Several binders in one header all take the ambient default.
theorem k3 {α₀ α₁ α₂ : Type} [OFE α₀] [OFE α₁] [OFE α₂] : True := trivial

/-- info: @k3 : ∀ {SI : Type u_1} [instSI : SIdx SI] {α₀ α₁ α₂ : Type} [OFE α₀] [OFE α₁] [OFE α₂], True -/
#guard_msgs in
#check @k3

end

/-! ## The fallback is only a fallback

Outside the section there is no `DefaultSI` at all, and unification still determines `SI`. -/

instance instSIdxNat : SIdx Nat := ⟨(· < ·)⟩
instance instSIdxBool : SIdx Bool := ⟨fun _ _ => True⟩

theorem pinned {α : Type} [OFE (SI := Nat) α] : True := trivial

/-- info: @pinned : ∀ {α : Type} [OFE α], True -/
#guard_msgs in
#check @pinned

-- With nothing to determine it, the tactic's own failure is reported rather than
-- "don't know how to synthesize implicit argument".
/--
error: could not synthesize default value for parameter 'SI' using tactics
---
error: failed to synthesize instance of type class
  DefaultSI ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
theorem undetermined {α : Type} [OFE α] : True := trivial

/-! ## Nested synthesis subgoals do not get the fallback

Like `@[default_instance]`, a binder fallback lives in the term elaborator, so an `OFE ?SI α`
arising as a *subgoal* of instance synthesis gets neither. Here the ambient default is `Nat`: a
surface occurrence takes it, while the same query reached through `Wrap` picks `Bool` instead.
Substituting a `@[default_instance]` formulation gives the same two answers, so this pins existing
behaviour rather than a regression. -/

instance : DefaultSI Nat := ⟨instSIdxNat⟩

instance boolOFE : OFE (SI := Bool) Unit :=
  ⟨fun _ _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
instance natOFE : OFE (SI := Nat) Unit :=
  ⟨fun _ _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

class Wrap (α : Type) where dummy : Unit

set_option synthInstance.checkSynthOrder false in
instance wrapOfOFE {SI : Type} [SIdx SI] {α : Type} [OFE (SI := SI) α] : Wrap α := ⟨()⟩

/--
info: @inferInstance (@OFE (@defaultSI Nat instDefaultSINat) instSIdxNat Unit)
  natOFE : @OFE (@defaultSI Nat instDefaultSINat) instSIdxNat Unit
-/
#guard_msgs in
set_option pp.explicit true in
#check (inferInstance : OFE Unit)

/-- info: @inferInstance (Wrap Unit) (@wrapOfOFE Bool instSIdxBool Unit boolOFE) : Wrap Unit -/
#guard_msgs in
set_option pp.explicit true in
#check (inferInstance : Wrap Unit)
