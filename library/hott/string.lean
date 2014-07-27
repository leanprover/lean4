-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import bool

namespace string
inductive char : Type :=
| ascii : bool → bool → bool → bool → bool → bool → bool → bool → char

inductive string : Type :=
| empty : string
| str   : char → string → string
end
