------------------------------------------------------------------------------------------------------ Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.classes.inhabited

inductive option (A : Type) : Type :=
| none {} : option A
| some    : A → option A

theorem inhabited_option [instance] (A : Type) : inhabited (option A) :=
inhabited_intro none
