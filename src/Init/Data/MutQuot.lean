prelude
import Init.Core
import Init.Data.List
import Init.System.IO

import Init.Data.Nat.Basic
import Init.Data.Fin.Basic
import Init.Data.UInt
import Init.Data.Repr
import Init.Data.ToString
import Init.Control.Id
import Init.Util

-- #print prefix Quot

universes u v w

namespace Mutable

structure Quot {α : Type u} (r : α → α → Prop) : Type u :=
mk' :: (toQuot : _root_.Quot r)

def Trunc (α : Type u) : Type u := Quot (fun (_ _ : α) => True)

instance {α : Type u} [Inhabited α] (r : α → α → Prop) : Inhabited (Quot r) :=
⟨ ⟨ _root_.Quot.mk r $ arbitrary _ ⟩ ⟩

namespace Quot
variables {α : Type u} {r : α → α → Prop}

/-
override mk, mk', toQuot
-/

unsafe def unsafeMk'  (r : α → α → Prop) (x : _root_.Quot r) : Mutable.Quot r :=
let inst : Inhabited (Mutable.Quot r) := ⟨ ⟨ x ⟩ ⟩;
match unsafeIO $ IO.Prim.mkRef (unsafeCast x : Nat) with
| Except.ok r => unsafeCast r
| Except.error _ => panic!"cannot create new reference"

unsafe def unsafeMk (r : α → α → Prop) (x : α) : Mutable.Quot r :=
unsafeMk' r (Quot.mk r x)

@[implementedBy Mutable.Quot.unsafeMk]
def mk (r : α → α → Prop) (x : α) : Quot r := ⟨ Quot.mk r x  ⟩

attribute [implementedBy Mutable.Quot.unsafeMk'] mk'

unsafe def unsafeLift {r : α → α → Prop} {β : Sort v} (f : α → β)
  (h : ∀ (a b : α), r a b → f a = f b) (x : Mutable.Quot r) : β :=
match unsafeIO $ IO.Prim.Ref.get (unsafeCast x : IO.Ref α) with
| Except.ok val => f val
| Except.error e =>
let inst : Inhabited β := ⟨x.toQuot.lift _ h⟩;
panic!"failed to read reference"

@[implementedBy unsafeLift]
def lift {β : Sort v} (f : α → β)
  (h : ∀ (a b : α), r a b → f a = f b) : Mutable.Quot r → β
| ⟨x⟩ => _root_.Quot.lift f h x

def ind {β : Quot r → Prop}
  (h : ∀ (a : α), β (mk r a)) : ∀ (q : Quot r), β q
| ⟨x⟩ => _root_.Quot.ind h x

def toQuotAux : Mutable.Quot r → _root_.Quot r :=
lift (_root_.Quot.mk r) (λ a b h => Quot.sound h)

attribute [implementedBy Mutable.Quot.toQuotAux] toQuot

def update {β : Sort v} (f : α → PProd β α)
  (ref : IO.Ref (ULift.{v} α)) : IO (ULift.{u} $ PLift.{v} β) := do
⟨x⟩ ← ref.get;
ref.reset;
let ⟨y,x'⟩ := f x;
ref.set ⟨x'⟩;
pure ⟨⟨y⟩⟩

unsafe def unsafeMutate {β : Sort v} (f : α → PProd β α)
  (h : ∀ (a b : α), r a b → (f a).1 = (f b).1)
  (h' : ∀ (a : α), r a (f a).2) (ref : Quot r) : β :=
match unsafeIO (update f $ unsafeCast ref) with
| Except.ok ⟨⟨x⟩⟩ => x
| Except.error _ =>
let inst : Inhabited β := ⟨ref.toQuot.lift _ h⟩;
panic!"failed IO in mutable quotient"

@[implementedBy unsafeMutate]
def mutate {β : Sort v} (f : α → PProd β α)
  (h : ∀ (a b : α), r a b → (f a).1 = (f b).1)
  (h' : ∀ (a : α), r a (f a).2) : Quot r → β :=
lift _ h

end Quot

end Mutable
