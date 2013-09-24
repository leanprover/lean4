/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <unordered_map>
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "kernel/context.h"
#include "util/list.h"
#include "library/all/all.h"
#include "library/expr_pair.h"
#include "library/arith/nat.h"
#include "library/arith/arith.h"

namespace lean {

using subst_map = std::unordered_map<unsigned, expr>;

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

public:
    bool match(expr const & p, expr const & t, unsigned o, subst_map & s);
};
}
