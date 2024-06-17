/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Given an inductive datatype \c n in \c env, return declaration for
    <tt>n.below</tt> auxiliary construction for <tt>n.brec_on</t>
    (aka below recursion on).
*/
declaration mk_below(environment const & env, name const & n);

/** \brief Given an inductive datatype \c n in \c env, return declaration for
    <tt>n.ibelow</tt> auxiliary construction for <tt>n.brec_on</t>.
*/
declaration mk_ibelow(environment const & env, name const & n);

/** \brief Given an inductive datatype \c n in \c env, return declaration for
    <tt>n.brec_on</tt>.
*/
declaration mk_brec_on(environment const & env, name const & n);

/** \brief Given an inductive datatype \c n in \c env, return declaration for
    <tt>n.binduction_on</tt>.
*/
declaration mk_binduction_on(environment const & env, name const & n);
}
