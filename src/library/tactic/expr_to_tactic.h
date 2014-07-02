/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/pos_info_provider.h"
#include "library/tactic/tactic.h"

namespace lean {
class expr_to_tactic_exception : public exception {
    expr m_expr;
public:
    expr_to_tactic_exception(expr const & e, char const * msg):exception(msg), m_expr(e) {}
    expr const & get_expr() const { return m_expr; }
};

typedef std::function<tactic(environment const & env, expr const & e, pos_info_provider const *)> expr_to_tactic_fn;
void register_expr_to_tactic(name const & n, expr_to_tactic_fn const & fn);
struct register_tac {
    register_tac(name const & n, expr_to_tactic_fn fn) { register_expr_to_tactic(n, fn); }
};
struct register_simple_tac {
    register_simple_tac(name const & n, std::function<tactic()> f);
};
struct register_bin_tac {
    register_bin_tac(name const & n, std::function<tactic(tactic const &, tactic const &)> f);
};
struct register_unary_tac {
    register_unary_tac(name const & n, std::function<tactic(tactic const &)> f);
};

tactic expr_to_tactic(environment const & env, expr const & e, pos_info_provider const *p);
expr mk_by(expr const & e);
bool is_by(expr const & e);
expr const & get_by_arg(expr const & e);
}
