/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/lbool.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "library/old_type_checker.h"
#include "library/old_converter.h"
#include "library/old_default_converter.h"


namespace lean {
static no_delayed_justification * g_no_delayed_jst = nullptr;

pair<bool, constraint_seq> old_converter::is_def_eq(expr const & t, expr const & s, old_type_checker & c) {
    return is_def_eq(t, s, c, *g_no_delayed_jst);
}

pair<expr, constraint_seq> old_converter::infer_type(old_type_checker & tc, expr const & e) { return tc.infer_type(e); }

/** \brief Do nothing old_converter */
struct dummy_old_converter : public old_converter {
    virtual pair<expr, constraint_seq> whnf(expr const & e, old_type_checker &) {
        return mk_pair(e, constraint_seq());
    }
    virtual pair<bool, constraint_seq> is_def_eq(expr const &, expr const &, old_type_checker &, delayed_justification &) {
        return mk_pair(true, constraint_seq());
    }
    virtual bool is_opaque(declaration const &) const { return false; }
    virtual optional<declaration> is_delta(expr const &) const { return optional<declaration>(); }
    virtual optional<expr> is_stuck(expr const &, old_type_checker &) { return none_expr(); }
};

std::unique_ptr<old_converter> mk_dummy_old_converter() {
    return std::unique_ptr<old_converter>(new dummy_old_converter());
}

void initialize_old_converter() {
    g_no_delayed_jst      = new no_delayed_justification();
}

void finalize_old_converter() {
    delete g_no_delayed_jst;
}
}
