/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Attributes

public section

namespace Lean

private def isValidCppId (id : String) : Bool :=
  let first := id.front;
  first.isAlpha  && (id.toRawSubstring.drop 1).all (fun c => c.isAlpha || c.isDigit || c == '_')

private def isValidCppName : Name → Bool
  | .str .anonymous s => isValidCppId s
  | .str p s          => isValidCppId s && isValidCppName p
  | _                 => false

/--
Exports a function under the provided unmangled symbol name. This can be used to refer to Lean
functions from other programming languages like C.

Example:
```
@[export lean_color_from_map]
def colorValue (properties : @& Std.HashMap String String) : UInt32 :=
  match properties["color"]? with
  | some "red" => 0xff0000
  | some "green" => 0x00ff00
  | some "blue" => 0x0000ff
  | _ => -1
```
C code:
```c
#include <lean/lean.h>

uint32_t lean_color_from_map(b_lean_obj_arg properties);

void fill_rectangle_from_map(b_lean_obj_arg properties) {
    uint32_t color = lean_color_from_map(properties);
    // ...
}
```

The opposite of this is `@[extern]`, which allows Lean functions to refer to functions from other
programming languages.
-/
@[builtin_doc]
builtin_initialize exportAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `export,
    descr := "name to be used by code generators",
    getParam := fun _ stx => do
      let exportName ← Attribute.Builtin.getId stx
      unless isValidCppName exportName do
        throwError "Invalid `export` function name: `{exportName}` is not a valid C++ identifier"
      return exportName
  }

@[export lean_get_export_name_for]
def getExportNameFor? (env : Environment) (n : Name) : Option Name :=
  exportAttr.getParam? env n

def isExport (env : Environment) (n : Name) : Bool :=
  -- The main function morally is an exported function as well. In particular,
  -- it should not participate in borrow inference.
  (getExportNameFor? env n).isSome || n == `main

end Lean
