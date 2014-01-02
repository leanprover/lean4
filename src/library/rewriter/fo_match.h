/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include "util/scoped_map.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "library/printer.h"

namespace lean {
using subst_map = scoped_map<unsigned, expr>;

class fo_match {
private:
    bool match_var(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_constant(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_value(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_app(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_lambda(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_pi(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_type(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_eq(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_let(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_metavar(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_main(expr const & p, expr const & t, unsigned o, subst_map & s);
    bool match_main(optional<expr> const & p, optional<expr> const & t, unsigned o, subst_map & s);

public:
    bool match(expr const & p, expr const & t, unsigned o, subst_map & s);
};
}
