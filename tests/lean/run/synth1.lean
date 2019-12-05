import Init.Lean.Meta
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

def print {α} [HasToString α] (a : α) : MetaM Unit :=
trace! `Meta.synthInstance (toString a)

set_option trace.Meta.synthInstance true
set_option trace.Meta.synthInstance.tryResolve false

def tst1 : MetaM Unit :=
do inst ← mkAppM `HasCoerce #[mkConst `Nat, mkSort levelZero];
   r ← synthInstance inst;
   print r

#eval tst1
