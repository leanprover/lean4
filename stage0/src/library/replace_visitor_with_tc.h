/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/replace_visitor.h"
#include "library/type_context.h"
namespace lean {
/** \brief Version of replace_visitor with a nested type_context_old object. */
class replace_visitor_with_tc : public replace_visitor {
protected:
    type_context_old & m_ctx;
    expr visit_lambda_pi_let(bool is_lam, expr const & e);
    virtual expr visit_lambda(expr const & e) override {
        return visit_lambda_pi_let(true, e);
    }
    virtual expr visit_let(expr const & e) override {
        return visit_lambda_pi_let(true, e);
    }
    virtual expr visit_pi(expr const & e) override {
        return visit_lambda_pi_let(false, e);
    }
    virtual expr visit_app(expr const & e) override;
public:
    replace_visitor_with_tc(type_context_old & ctx):m_ctx(ctx) {}
};
}
