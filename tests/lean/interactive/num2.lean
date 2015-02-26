----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------
import logic.inhabited

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive pos_num : Type :=
one  : pos_num|
bit1 : pos_num → pos_num|
bit0 : pos_num → pos_num

theorem pos_num.is_inhabited [instance] : inhabited pos_num :=
inhabited.mk pos_num.one

namespace pos_num
  definition inc (a : pos_num) : pos_num :=
  rec (bit0 one) (λn r, bit0 r) (λn r, bit1 n) a

  definition num_bits (a : pos_num) : pos_num :=
  rec one (λn r, inc r) (λn r, inc r) a
end pos_num

inductive num : Type :=
zero  : num,
pos   : pos_num → num

theorem num.is_inhabited [instance] : inhabited num :=
inhabited.mk num.zero

namespace num
  definition inc (a : num) : num :=
  rec (pos pos_num.one) (λp, pos (pos_num.inc p)) a

  definition num_bits (a : num) : num :=
  rec (pos pos_num.one) (λp, pos (pos_num.num_bits p)) a
end num
