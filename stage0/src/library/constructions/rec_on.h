/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Given an inductive datatype \c n in \c env, returns
    the declaration for <tt>n.rec_on</tt>.

    \remark <tt>rec_on</tt> is based on <tt>n.rec</tt>

    \remark Throws an exception if \c n is not an inductive datatype.
*/
declaration mk_rec_on(environment const & env, name const & n);
}
