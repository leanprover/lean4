/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"

namespace lean {
/** \brief Given an inductive datatype \c n (which is not a proposition) in \c env,
    returns the declaration for <tt>n.no_confusion_type</tt>.

    \remark This procedure assumes the environment contains <tt>eq, n.cases_on</tt>.
    If the environment has an impredicative Prop, it also assumes heq is defined.
    If the environment does not have an impredicative Prop, then it also assumes lift is defined.
*/
declaration mk_no_confusion_type(elab_environment const & env, name const & n);

/** \brief Given an inductive datatype \c n (which is not a proposition) in \c env,
    returns the declaration for <tt>n.no_confusion</tt>.

    \remark This procedure assumes the environment contains <tt>eq, n.cases_on, n.no_confusion_type</tt>.
    If the environment has an impredicative Prop, it also assumes heq is defined.
    If the environment does not have an impredicative Prop, then it also assumes lift is defined.
*/
declaration mk_no_confusion(elab_environment const & env, name const & n);
}
