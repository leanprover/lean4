import Lean.Meta

open Lean
open Lean.Meta

class HasCoerce (a b : Type) :=
(coerce : a → b)

def coerce {a b : Type} [HasCoerce a b] : a → b :=
@HasCoerce.coerce a b _

instance coerceTrans {a b c : Type} [HasCoerce b c] [HasCoerce a b] : HasCoerce a c :=
⟨fun x => coerce (coerce x : b)⟩

instance coerceBoolToProp : HasCoerce Bool Prop :=
⟨fun y => y = true⟩

instance coerceDecidableEq (x : Bool) : Decidable (coerce x) :=
inferInstanceAs (Decidable (x = true))

instance coerceNatToBool : HasCoerce Nat Bool :=
⟨fun x => x == 0⟩

instance coerceNatToInt : HasCoerce Nat Int :=
⟨fun x => Int.ofNat x⟩

def print {α} [ToString α] (a : α) : MetaM Unit := do
trace[Meta.synthInstance] (toString a)


def tst1 : MetaM Unit := do
let inst ← mkAppM `HasCoerce #[mkConst `Nat, mkSort levelZero]
let r ← synthInstance inst
print r

set_option trace.Meta.synthInstance true in
set_option trace.Meta.synthInstance.tryResolve false in
#eval tst1

def tst2 : MetaM Unit := do
let inst ← mkAppM `Bind #[mkConst `IO]
-- globalInstances ← getGlobalInstances
-- print (format globalInstances)
-- result ← globalInstances.getUnify inst
-- print result
let r ← synthInstance inst
print r
pure ()

set_option trace.Meta.synthInstance true in
set_option trace.Meta.synthInstance.tryResolve false in
#eval tst2

def tst3 : MetaM Unit := do
let inst ← mkAppM `BEq #[mkConst `Nat]
let r ← synthInstance inst
print r
pure ()

set_option trace.Meta.synthInstance true in
set_option trace.Meta.synthInstance.tryResolve false in
#eval tst3
