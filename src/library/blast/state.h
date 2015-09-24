/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "kernel/expr.h"
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
class metavar_decl {
    hypothesis_set m_context;
    expr           m_type;
};

class state {
    typedef rb_map<unsigned, metavar_decl, unsigned_cmp> metavar_decls;
    metavar_decls m_metavar_decls;
};
}}
