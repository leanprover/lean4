/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
-- DO NOT EDIT: file generated using the scripts/unicode tool
prelude
import Init.Data.Nat.Basic

namespace Char

/--
The `unicodeVersion` definition gives Lean's current version of Unicode in format (major,minor,update). 

                         New versions of Unicode are released regularly and subsequently all methods 

                         in the standard library depending on Unicode are updated. Therefore the behavior 

                          of some `Char` and `String` methods and the value of this constant changes 

                          over time. *This is not considered to be a breaking change.*
-/
def unicodeVersion : Nat × Nat × Nat := (15,1,0)

end Char
