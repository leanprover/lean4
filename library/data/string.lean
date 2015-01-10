/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.string
Author: Leonardo de Moura
-/
import data.bool
open bool

protected definition char.is_inhabited [instance] : inhabited char :=
inhabited.mk (char.mk ff ff ff ff ff ff ff ff)

protected definition string.is_inhabited [instance] : inhabited string :=
inhabited.mk string.empty
