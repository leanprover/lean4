/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/occurs.h"
#include "kernel/metavar.h"
#include "kernel/expr_maps.h"
#include "kernel/replace_visitor.h"
#include "library/placeholder.h"

namespace lean {
static name g_placeholder_name("_");
expr mk_placeholder() {
    return mk_constant(g_placeholder_name);
}

bool is_placeholder(expr const & e) {
    return is_constant(e) && const_name(e) == g_placeholder_name;
}

bool has_placeholder(expr const & e) {
    return occurs(mk_placeholder(), e);
}

class replace_placeholders_with_metavars_proc : public replace_visitor {
    metavar_env &    m_menv;
    expr_map<expr> * m_new2old;
protected:
    expr visit_constant(expr const & e, context const & c) {
        if (is_placeholder(e)) {
            return m_menv.mk_metavar(c);
        } else {
            return e;
        }
    }

    expr visit(expr const & e, context const & c) {
        expr r = replace_visitor::visit(e, c);
        if (!is_eqp(r, e) && m_new2old)
            (*m_new2old)[r] = e;
        return r;
    }
public:
    replace_placeholders_with_metavars_proc(metavar_env & menv, expr_map<expr> * new2old):
        m_menv(menv),
        m_new2old(new2old) {
    }
};

expr replace_placeholders_with_metavars(expr const & e, metavar_env & menv, expr_map<expr> * new2old) {
    replace_placeholders_with_metavars_proc proc(menv, new2old);
    return proc(e);
}
}
