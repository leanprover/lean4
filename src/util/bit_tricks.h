/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
inline bool is_power_of_two(unsigned v) { return !(v & (v - 1)) && v; }
unsigned log2(unsigned v);
double log2(int v);
}
