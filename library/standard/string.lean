-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import bit
using bit

namespace string
inductive char : Type :=
| ascii : bit → bit → bit → bit → bit → bit → bit → bit → char

inductive string : Type :=
| empty : string
| str   : char → string → string

theorem inhabited_char [instance] : inhabited char
:= inhabited_intro (ascii b0 b0 b0 b0 b0 b0 b0 b0)

theorem inhabited_string [instance] : inhabited string
:= inhabited_intro empty
end
