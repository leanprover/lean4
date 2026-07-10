module

/-!
Tests relocatable UTF-8 data segments and runtime string construction.
-/

@[extern "lean_wasm_string_byte_size"]
opaque stringByteSize (value : @& String) : UInt32

@[noinline] def greeting (_ : UInt32) : String :=
  "héllo"

@[export lean_wasm_string_size]
def stringSize (x : UInt32) : UInt32 :=
  stringByteSize (greeting x)
