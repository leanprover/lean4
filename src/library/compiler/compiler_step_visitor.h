/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/replace_visitor.h"

namespace lean {
/** \brief Replace visitor class for compiler steps.
    Types are ignored during compilation steps. */
class compiler_step_visitor : public replace_visitor {
protected:
    environment  m_env;
    type_context_old m_ctx;

    expr visit_lambda_let(expr const & e);
protected:
    compiler_step_visitor(environment const & env, abstract_context_cache & cache);
    virtual ~compiler_step_visitor();

    environment const & env() const { return m_env; }
    type_context_old & ctx() { return m_ctx; }

    virtual expr visit_macro(expr const & e) override;

    virtual expr visit_pi(expr const & e) override {
        /* Compiler steps ignore types. */
        return e;
    }

    virtual expr visit_local(expr const & e) override {
        /* We don't need to visit the type since we are using type_context_old. */
        return e;
    }

    virtual expr visit_meta(expr const &) override {
        /* We only compile fully elaborated terms. */
        lean_unreachable();
    }

    virtual expr visit_var(expr const &) override {
        /* We only visit closed terms. */
        lean_unreachable();
    }

    virtual expr visit_app(expr const & e) override;
    virtual expr visit_let(expr const & e) override;
    virtual expr visit_lambda(expr const & e) override;
};
}
