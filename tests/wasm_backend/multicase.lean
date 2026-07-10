module

/-!
Tests wasm32 tag dispatch for inductives with more than two constructors.
-/

inductive Choice where
  | first
  | second
  | third

@[noinline] def choiceValue : Choice → UInt32
  | .first => 11
  | .second => 22
  | .third => 33

def multicase (tag : UInt32) : UInt32 :=
  let choice := if tag == 0 then Choice.first else if tag == 1 then Choice.second else Choice.third
  choiceValue choice

@[export lean_wasm_multicase_0] def multicase0 : UInt32 := multicase 0
@[export lean_wasm_multicase_1] def multicase1 : UInt32 := multicase 1
@[export lean_wasm_multicase_2] def multicase2 : UInt32 := multicase 2
