module

set_option warn.sorry false

public class X
instance : X := sorry
public instance : X := sorry
instance : X := sorry

namespace InNamespace
public class Y
instance : Y := sorry
public instance : Y := sorry
instance : Y := sorry
end InNamespace


inductive Day where
  | mo | tu | we
deriving Repr

def Day.succ? : Day → Option Day
  | mo => some tu
  | tu => some we
  | we => none

instance : Std.PRange.UpwardEnumerable Day where
  succ? := Day.succ?

def Day.toNat : Day → Nat
  | mo => 0
  | tu => 1
  | we => 2

instance : LT Day where
  lt _ _ := True

instance : LE Day where
  le _ _ := True

instance : Std.Rxo.IsAlwaysFinite Day where
  finite init hi := ⟨3, by sorry⟩

instance : Std.Rxi.IsAlwaysFinite Day where
  finite init := ⟨3, by sorry⟩

instance : Std.Rxc.IsAlwaysFinite Day where
  finite init hi := ⟨3, by sorry⟩
