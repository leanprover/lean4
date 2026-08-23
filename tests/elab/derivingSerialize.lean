import Lean.Data.Json.Derse

/-!
Tests the deriving handler for `Std.Internal.Derse.Serialize` by checking the emitted JSON against
the encoding documented in `tests/compile_bench/derse.lean`: structures become objects,
constructors without fields become bare strings, constructors whose fields all have user names
become `{"ctor":{"field":…}}` objects and constructors with positional fields become `{"ctor":[…]}`
arrays.
-/

open Std.Internal.Derse

def checkSer [Serialize α] (obj : α) (expected : String) : IO Unit := do
  let got := Json.toString obj CompactFormatter.mk
  unless got == expected do
    throw <| .userError s!"got {got}, expected {expected}"

structure Foo where
  x : Nat
  y : String
  deriving Serialize

#eval checkSer { x := 1, y := "bla" : Foo } "{\"x\":1,\"y\":\"bla\"}"

structure NoFields where
  deriving Serialize

#eval checkSer NoFields.mk "{}"

structure Author where
  name : String
  email : Option String
  id : UInt64
  deriving Serialize

#eval checkSer { name := "Jane", email := none, id := 7 : Author }
  "{\"name\":\"Jane\",\"email\":null,\"id\":\"7\"}"
#eval checkSer { name := "Jane", email := some "jane@example.com", id := 7 : Author }
  "{\"name\":\"Jane\",\"email\":\"jane@example.com\",\"id\":\"7\"}"

structure WInfo where
  a : Nat
  b : Nat
  deriving Serialize

inductive E where
  | W : WInfo → E
  | WAlt (a b : Nat)
  | X : Nat → Nat → E
  | Y : Nat → E
  | YAlt (a : Nat)
  | Z
  deriving Serialize

#eval checkSer (E.W { a := 2, b := 3 }) "{\"W\":{\"a\":2,\"b\":3}}"
#eval checkSer (E.WAlt 2 3) "{\"WAlt\":{\"a\":2,\"b\":3}}"
#eval checkSer (E.X 2 3) "{\"X\":[2,3]}"
#eval checkSer (E.Y 4) "{\"Y\":4}"
#eval checkSer (E.YAlt 5) "{\"YAlt\":{\"a\":5}}"
#eval checkSer E.Z "\"Z\""

inductive ERec where
  | mk : Nat → ERec
  | W : ERec → ERec
  deriving Serialize

#eval checkSer (ERec.mk 6) "{\"mk\":6}"
#eval checkSer (ERec.W (ERec.mk 6)) "{\"W\":{\"mk\":6}}"

inductive ENest where
  | mk : Nat → ENest
  | W : Array ENest → ENest
  deriving Serialize

#eval checkSer (ENest.W #[ENest.mk 9, ENest.mk 10]) "{\"W\":[{\"mk\":9},{\"mk\":10}]}"

inductive EParam (α : Type) where
  | mk : α → EParam α
  deriving Serialize

#eval checkSer (EParam.mk 12) "{\"mk\":12}"
#eval checkSer (EParam.mk "abcd") "{\"mk\":\"abcd\"}"

mutual
inductive M1 where
  | base : Nat → M1
  | ofM2 : M2 → M1
inductive M2 where
  | wrap : M1 → M2
end

deriving instance Serialize for M1, M2

#eval checkSer (M1.ofM2 (M2.wrap (M1.base 3))) "{\"ofM2\":{\"wrap\":{\"base\":3}}}"
#eval checkSer (M2.wrap (M1.base 4)) "{\"wrap\":{\"base\":4}}"

-- `?`-suffixed `Option` fields follow the `ToJson` convention: serialized without the suffix and
-- omitted entirely when `none`.
structure OptFields where
  a : Nat
  b? : Option Nat
  c : Nat
  deriving Serialize

#eval checkSer { a := 1, b? := some 2, c := 3 : OptFields } "{\"a\":1,\"b\":2,\"c\":3}"
#eval checkSer { a := 1, b? := none, c := 3 : OptFields } "{\"a\":1,\"c\":3}"

-- The generated code must not rely on auto-bound implicits.
set_option autoImplicit false in
structure StrictOpts where
  n : Nat
  deriving Serialize

#eval checkSer { n := 5 : StrictOpts } "{\"n\":5}"
