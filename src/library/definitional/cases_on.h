/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Given an inductive datatype \c n in \c env, add
    <tt>n.cases_on</tt> to the environment.

    \remark Throws an exception if \c n is not an inductive datatype.
*/
environment mk_cases_on(environment const & env, name const & n);
}
