/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/lbool.h"
#include "kernel/converter.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/type_checker.h"
#include "kernel/default_converter.h"

namespace lean {
static no_delayed_justification * g_no_delayed_jst = nullptr;

pair<bool, constraint_seq> converter::is_def_eq(expr const & t, expr const & s, type_checker & c) {
    return is_def_eq(t, s, c, *g_no_delayed_jst);
}

name converter::mk_fresh_name(type_checker & tc) { return tc.mk_fresh_name(); }

pair<expr, constraint_seq> converter::infer_type(type_checker & tc, expr const & e) { return tc.infer_type(e); }

extension_context & converter::get_extension(type_checker & tc) { return tc.get_extension(); }


/** \brief Do nothing converter */
struct dummy_converter : public converter {
    virtual pair<expr, constraint_seq> whnf(expr const & e, type_checker &) {
        return mk_pair(e, constraint_seq());
    }
    virtual pair<bool, constraint_seq> is_def_eq(expr const &, expr const &, type_checker &, delayed_justification &) {
        return mk_pair(true, constraint_seq());
    }
    virtual bool is_opaque(declaration const &) const { return false; }
    virtual optional<declaration> is_delta(expr const &) const { return optional<declaration>(); }
    virtual bool is_stuck(expr const &, type_checker &) { return false; }
};

std::unique_ptr<converter> mk_dummy_converter() {
    return std::unique_ptr<converter>(new dummy_converter());
}

void initialize_converter() {
    g_no_delayed_jst      = new no_delayed_justification();
}

void finalize_converter() {
    delete g_no_delayed_jst;
}
}
