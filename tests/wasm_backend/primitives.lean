module

/-!
Tests expanded WebAssembly scalar primitive lowering (div/mod/bitwise/shifts/compare).
-/

@[export lean_wasm_prim_div]
def primDiv (x y : UInt32) : UInt32 := x / y

@[export lean_wasm_prim_mod]
def primMod (x y : UInt32) : UInt32 := x % y

@[export lean_wasm_prim_and]
def primAnd (x y : UInt32) : UInt32 := x &&& y

@[export lean_wasm_prim_or]
def primOr (x y : UInt32) : UInt32 := x ||| y

@[export lean_wasm_prim_xor]
def primXor (x y : UInt32) : UInt32 := x ^^^ y

@[export lean_wasm_prim_shl]
def primShl (x y : UInt32) : UInt32 := x <<< y

@[export lean_wasm_prim_shr]
def primShr (x y : UInt32) : UInt32 := x >>> y
