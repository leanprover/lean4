-- Copyright (c) 2016 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.string
set_option new_elaborator true

/- This function has a native implementation that displays the given string in the regular output stream. -/
definition trace {A : Type} (s : string) (f : unit → A) : A :=
f ()
