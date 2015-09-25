/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "kernel/expr.h"
#include "library/blast/hypothesis.h"
#include "library/blast/branch.h"

namespace lean {
namespace blast {
class metavar_decl {
    hypothesis_set m_context;
    expr           m_type;
public:
    metavar_decl() {}
    metavar_decl(hypothesis_set const & c, expr const & t):m_context(c), m_type(t) {}
};

class state {
    friend class context;
    unsigned m_next_mref_index;
    typedef rb_map<unsigned, metavar_decl, unsigned_cmp> metavar_decls;
    typedef rb_map<unsigned, expr, unsigned_cmp>         assignment;
    metavar_decls m_metavar_decls;
    assignment    m_assignment;
public:
    state();
    unsigned add_metavar_decl(metavar_decl const & decl);
    metavar_decl const * get_metavar_decl(unsigned idx) const { return m_metavar_decls.find(idx); }
    metavar_decl const * get_metavar_decl(expr const & e) const { return get_metavar_decl(mref_index(e)); }
};
}}
