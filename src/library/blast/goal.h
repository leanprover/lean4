/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "library/blast/expr.h"
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
class goal {
    typedef rb_map<unsigned, hypothesis, unsigned_cmp> context;
    friend class state;
    unsigned      m_next;
    context       m_context;
    expr          m_type;
    expr const & mk_lref(expr const & type, optional<expr> const & value);
public:
    goal():m_next(0) {}
    hypothesis const * get(unsigned idx) const { return m_context.find(idx); }
    hypothesis const * get(expr const & e) const {
        lean_assert(is_lref(e));
        return get(get_lmindex(e));
    }
};
}}
