-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import data.bool

using bool inhabited

namespace string

inductive char : Type :=
| ascii : bool → bool → bool → bool → bool → bool → bool → bool → char

inductive string : Type :=
| empty : string
| str   : char → string → string

theorem char_inhabited [instance] : inhabited char :=
inhabited_mk (ascii ff ff ff ff ff ff ff ff)

theorem string_inhabited [instance] : inhabited string :=
inhabited_mk empty

end string
