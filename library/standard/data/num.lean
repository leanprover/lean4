----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.classes.inhabited

namespace num

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive pos_num : Type :=
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

inductive num : Type :=
| zero  : num
| pos   : pos_num → num

theorem inhabited_pos_num [instance] : inhabited pos_num :=
inhabited_intro one

theorem inhabited_num [instance] : inhabited num :=
inhabited_intro zero

end