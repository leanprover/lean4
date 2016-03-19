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
expr converter::infer_type(type_checker & tc, expr const & e) { return tc.infer_type(e); }

/** \brief Do nothing converter */
struct dummy_converter : public converter {
    virtual expr whnf(expr const & e, type_checker &) {
        return e;
    }
    virtual bool is_def_eq(expr const &, expr const &, type_checker &) {
        return true;
    }
    virtual bool is_opaque(declaration const &) const { return false; }
    virtual optional<declaration> is_delta(expr const &) const { return optional<declaration>(); }
    virtual optional<expr> is_stuck(expr const &, type_checker &) { return none_expr(); }
};

std::unique_ptr<converter> mk_dummy_converter() {
    return std::unique_ptr<converter>(new dummy_converter());
}

void initialize_converter() {
}

void finalize_converter() {
}
}
