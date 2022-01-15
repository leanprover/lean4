constant SPointed : NonemptyType
def S : Type := SPointed.type
instance : Nonempty S := SPointed.property

@[extern "lean_mk_S"] constant mkS (x y : UInt32) (s : @& String) : S
@[extern "lean_S_add_x_y"] constant S.addXY (s : @& S) : UInt32
@[extern "lean_S_string"] constant S.string (s : @& S) : String
-- The following 3 externs have side effects. Thus, we put them in IO.
@[extern "lean_S_global_append"] constant appendToGlobalS (str : @& String) : IO Unit
@[extern "lean_S_global_string"] constant getGlobalString : IO String
@[extern "lean_S_update_global"] constant updateGlobalS (s : @& S) : IO Unit
