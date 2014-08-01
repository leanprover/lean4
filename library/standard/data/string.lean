------------------------------------------------------------------------------------------------------ Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import data.bool
using bool

namespace string
inductive char : Type :=
| ascii : bool → bool → bool → bool → bool → bool → bool → bool → char

inductive string : Type :=
| empty : string
| str   : char → string → string

theorem inhabited_char [instance] : inhabited char :=
inhabited_intro (ascii ff ff ff ff ff ff ff ff)

theorem inhabited_string [instance] : inhabited string :=
inhabited_intro empty

end
