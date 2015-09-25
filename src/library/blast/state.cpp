/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/state.h"

namespace lean {
namespace blast {
state::state():m_next_mref_index(0) {}
unsigned state::add_metavar_decl(metavar_decl const & decl) {
    unsigned r = m_next_mref_index;
    m_next_mref_index++;
    m_metavar_decls.insert(r, decl);
    return r;
}
}}
