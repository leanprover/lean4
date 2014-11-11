/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Given an inductive datatype \c n in \c env, add
    <tt>n.brec_on</tt> (aka below recursion on) to the environment.
*/
environment mk_below(environment const & env, name const & n);
}
