/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
/** \brief Updated internal indices associated with declarations
    We track which constants occur in the type of other constants (and the inverse map).
    We also track the number of times a constant occur in the type of other constants.

    \remark This procedure will "unfold" reducible constants when computing statistics.
*/
environment update_decl_stats(environment const & env, declaration const & d);
/** \brief Return the number of constants s.t. \c n occur in their type. */
unsigned get_num_occs(environment const & env, name const & n);
/** \brief Return the set of constants that occur in the type of \c n. */
name_set get_use_set(environment const & env, name const & n);
/** \brief Return the set of constants s.t. \c n occur in their type. */
name_set get_used_by_set(environment const & env, name const & n);
void initialize_decl_stats();
void finalize_decl_stats();
}
