/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura

Declare new, simpler coercion class without the special support for transitivity.
Test that new tabled typeclass resolution deals with loops and diamonds correctly.
-/


class HasCoerce (a b : Type) :=
(coerce : a → b)

def coerce {a b : Type} [HasCoerce a b] : a → b :=
@HasCoerce.coerce a b _

instance coerceTrans {a b c : Type} [HasCoerce a b] [HasCoerce b c] : HasCoerce a c :=
⟨fun x => coerce (coerce x : b)⟩

instance coerceBoolToProp : HasCoerce Bool Prop :=
⟨fun y => y = true⟩

instance coerceDecidableEq (x : Bool) : Decidable (coerce x) :=
inferInstanceAs (Decidable (x = true))

instance coerceSubtype {a : Type} {p : a → Prop} : HasCoerce {x // p x} a :=
⟨Subtype.val⟩

instance liftCoerceFn {a₁ a₂ b₁ b₂ : Type} [HasCoerce a₂ a₁] [HasCoerce b₁ b₂] : HasCoerce (a₁ → b₁) (a₂ → b₂) :=
⟨fun f x => coerce (f (coerce x))⟩

instance liftCoerceFnRange {a b₁ b₂ : Type} [HasCoerce b₁ b₂] : HasCoerce (a → b₁) (a → b₂) :=
⟨fun f x => coerce (f x)⟩

instance liftCoerceFnDom {a₁ a₂ b : Type} [HasCoerce a₂ a₁] : HasCoerce (a₁ → b) (a₂ → b) :=
⟨fun f x => f (coerce x)⟩

instance liftCoercePair {a₁ a₂ b₁ b₂ : Type} [HasCoerce a₁ a₂] [HasCoerce b₁ b₂] : HasCoerce (a₁ × b₁) (a₂ × b₂) :=
⟨fun p => match p with
  | (x, y) => (coerce x,  coerce y)⟩

instance liftCoercePair₁ {a₁ a₂ b : Type} [HasCoerce a₁ a₂] : HasCoerce (a₁ × b) (a₂ × b) :=
⟨fun p => match p with
  | (x, y) => (coerce x, y)⟩

instance liftCoercePair₂ {a b₁ b₂ : Type} [HasCoerce b₁ b₂] : HasCoerce (a × b₁) (a × b₂) :=
⟨fun p => match p with
  | (x, y) => (x,  coerce y)⟩

instance liftCoerceList {a b : Type} [HasCoerce a b] : HasCoerce (List a) (List b) :=
⟨fun l => List.map (@coerce a b _) l⟩

-- Tests

axiom Bot (α : Type) (n : Nat) : Type
axiom Left (α : Type) (n : Nat) : Type
axiom Right (α : Type) (n : Nat) : Type
axiom Top (α : Type) (n : Nat) : Type

@[instance] axiom BotToTopSucc (α : Type) (n : Nat) : HasCoerce (Bot α n) (Top α n.succ)
@[instance] axiom TopSuccToBot (α : Type) (n : Nat) : HasCoerce (Top α n.succ) (Bot α n)
@[instance] axiom TopToRight (α : Type) (n : Nat) : HasCoerce (Top α n) (Right α n)
@[instance] axiom TopToLeft (α : Type) (n : Nat) : HasCoerce (Top α n) (Left α n)
@[instance] axiom LeftToTop (α : Type) (n : Nat) : HasCoerce (Left α n) (Top α n)
@[instance] axiom RightToTop (α : Type) (n : Nat) : HasCoerce (Right α n) (Top α n)
@[instance] axiom LeftToBot (α : Type) (n : Nat) : HasCoerce (Left α n) (Bot α n)
@[instance] axiom RightToBot (α : Type) (n : Nat) : HasCoerce (Right α n) (Bot α n)
@[instance] axiom BotToLeft (α : Type) (n : Nat) : HasCoerce (Bot α n) (Left α n)
@[instance] axiom BotToRight (α : Type) (n : Nat) : HasCoerce (Bot α n) (Right α n)

#print "-----"

set_option synthInstance.maxSize 256
set_option synthInstance.maxHeartbeats 500000

#synth HasCoerce (Top Unit Nat.zero)
                 (Top Unit Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)

#synth HasCoerce (Top Unit Nat.zero × Top Unit Nat.zero × Top Unit Nat.zero)
                 (Top Unit Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ
                  × Top Unit Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ
                  × Top Unit Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ)

#synth HasCoerce (Top Unit Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → Top Unit Nat.zero)
                 (Top Unit Nat.zero → Top Unit Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
