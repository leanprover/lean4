module
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.NameMangling
import Lean.Compiler.LCNF.ExplicitBoxing

/-!
# Test behavior of name mangling
-/

open Lean IR
open Lean.Compiler.LCNF (mkBoxedName)

def checkMangle (n : Name) (s : String) : IO Unit := do
  if n.mangle "" ≠ s then
    throw <| .userError s!"failed: {n} mangles to {n.mangle ""} but expected {s}"
  if .demangle s ≠ n then
    throw <| .userError s!"failed: {s} demangles to {Lean.Name.demangle s} but expected {n}"
  if n ≠ .anonymous ∧ mkMangledBoxedName s ≠ (mkBoxedName n).mangle "" then
    throw <| .userError s!"failed: {mkBoxedName n} mangles to {(mkBoxedName n).mangle ""} but \
      mkMangledBoxedName produced {mkMangledBoxedName s}"

/-!
Mangling simple identifiers with optional number components and preceding underscores.
-/

#eval checkMangle `ab12 "ab12"
#eval checkMangle ``Lean.Name.mangle "Lean_Name_mangle"
#eval checkMangle `Lean.Name.mangle._aux "Lean_Name_mangle___aux"
#eval checkMangle ((`_private.Lean.Compiler.NameMangling).num 0 ++ `Lean.Name.mangleAux)
    "__private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux"

/-!
Escape sequences in mangled identifiers.
-/

#eval checkMangle `«ÿ» "00_xff"
#eval checkMangle `«α₁» "00_u03b1_u2081"
#eval checkMangle `«𝒫» "00_U0001d4ab"

/-!
Escape sequence disambiguation
-/

#eval checkMangle `a' "a_x27"
#eval checkMangle `a.x27 "a_00x27"
#eval checkMangle `a_' "a___x27"
#eval checkMangle `a._x27 "a_00__x27"
#eval checkMangle `a.u0027 "a_00u0027"
#eval checkMangle `a.U00000027 "a_00U00000027"
#eval checkMangle `a.ucafe "a_00ucafe"
#eval checkMangle `a.uCAFE "a_uCAFE" -- uppercase does not need to be disambiguated

/-!
Trailing underscores in names
-/

#eval checkMangle `a._b "a___b"
#eval checkMangle `a_.b "a___00b"
#eval checkMangle `a_ "a__"
#eval checkMangle `a_.«» "a___00"
#eval checkMangle `a.__ "a_00____"

/-!
Empty name components
-/

#eval checkMangle `a_b "a__b"
#eval checkMangle `a.«».b "a_00_b"
#eval checkMangle `«».b "00_b"
#eval checkMangle `b_.«» "b___00"

/-!
Numbers vs numbers in text
-/

#eval checkMangle ((`a).num 2 ++ `b) "a_2__b"
#eval checkMangle `a.«2_b» "a_002__b"

/-!
Consecutive number components
-/

#eval checkMangle ((`a).num 2 |>.num 3 |>.str "" |>.num 4) "a_2__3__00_4_"

/-!
Preceding number components
-/

#eval checkMangle (.str (.num .anonymous 4) "hi") "4__hi"

/-!
Anonymous vs empty string
-/

#eval checkMangle .anonymous ""
#eval checkMangle `«» "00"
#eval checkMangle `«».«» "00_00"
