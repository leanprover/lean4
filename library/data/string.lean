/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.string
Author: Leonardo de Moura
-/

import data.bool
open bool inhabited

namespace char
  protected definition is_inhabited [instance] : inhabited char :=
  inhabited.mk (mk ff ff ff ff ff ff ff ff)
end char

namespace string
  protected definition is_inhabited [instance] : inhabited string :=
  inhabited.mk empty
end string
