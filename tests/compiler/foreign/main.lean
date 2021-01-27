constant SPointed : PointedType
def S : Type := SPointed.type
instance : Inhabited S := ⟨SPointed.val⟩

@[extern "lean_mk_S"] constant mkS (x y : UInt32) (s : @& String) : S
@[extern "lean_S_add_x_y"] constant S.addXY (s : @& S) : UInt32
@[extern "lean_S_string"] constant S.string (s : @& S) : String
-- The following 3 externs have side effects. Thus, we put them in IO.
@[extern "lean_S_global_append"] constant appendToGlobalS (str : @& String) : IO Unit
@[extern "lean_S_global_string"] constant getGlobalString : IO String
@[extern "lean_S_update_global"] constant updateGlobalS (s : @& S) : IO Unit

def main : IO Unit := do
IO.println (mkS 10 20 "hello").addXY;
IO.println (mkS 10 20 "hello").string;
appendToGlobalS "foo";
appendToGlobalS "bla";
getGlobalString >>= IO.println;
updateGlobalS (mkS 0 0 "world");
getGlobalString >>= IO.println;
pure ()
