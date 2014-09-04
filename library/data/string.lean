-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import data.bool

open bool inhabited

inductive char : Type :=
mk : bool → bool → bool → bool → bool → bool → bool → bool → char

inductive string : Type :=
empty : string,
str   : char → string → string

theorem char_inhabited [instance] : inhabited char :=
inhabited.mk (char.mk ff ff ff ff ff ff ff ff)

theorem string_inhabited [instance] : inhabited string :=
inhabited.mk string.empty
