/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
/** \brief Return v - k. It throws an exception if there is a underflow. */
int safe_sub(int v, int k);
int safe_sub(int v, unsigned k);

/** \brief Return v + k. It throws an exception if there is an overflow. */
int safe_add(int v, int k);
int safe_add(int v, unsigned k);
unsigned safe_add(unsigned v, unsigned k);
}
