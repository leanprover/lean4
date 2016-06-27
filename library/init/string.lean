/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.char init.list

definition string [reducible] := list char

namespace string
definition empty : string := list.nil
definition str : char → string → string := list.cons

definition concat (a b : string) : string :=
list.append b a
end string

definition string.has_append [instance] : has_append string :=
has_append.mk string.concat
