/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <unordered_map>
#include "kernel/expr.h"
#include "kernel/context.h"
#include "util/list.h"
#include "library/all/all.h"
#include "library/expr_pair.h"
#include "library/arith/nat.h"
#include "library/arith/arith.h"

namespace lean {

typedef std::unordered_map<unsigned, expr const &> subst_map;

class fo_match {
private:
    bool match_var(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_constant(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_value(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_app(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_lambda(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_pi(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_type(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_eq(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_let(context & ctx, expr const & p, expr const & t, subst_map & s);
    bool match_metavar(context & ctx, expr const & p, expr const & t, subst_map & s);
public:
    bool match(context & ctx, expr const & p, expr const & t, subst_map & s);
};
}
