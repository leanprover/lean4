-- Copyright (c) 2016 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.string

/- This function has a native implementation that tracks time. -/
def timeit {A : Type} (s : string) (f : unit → A) : A :=
f ()
