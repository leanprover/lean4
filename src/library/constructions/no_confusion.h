/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Given an inductive datatype \c n (which is not a proposition) in \c env, add
    <tt>n.no_confusion_type</tt> and <tt>n.no_confusion</tt> to the environment.

    \remark This procedure assumes the environment contains eq, n.cases_on</tt>.
    If the environment has an impredicative Prop, it also assumes heq is defined.
    If the environment does not have an impredicative Prop, then it also assumes lift is defined.
*/
environment mk_no_confusion(environment const & env, name const & n);
}
