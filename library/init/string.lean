/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.char

definition string [reducible] := list char

namespace string
definition empty : string := list.nil
definition str : char → string → string := list.cons
end string
