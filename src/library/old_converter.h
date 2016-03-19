/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/environment.h"
#include "library/constraint.h"
#include "library/justification.h"

namespace lean {
class old_type_checker;

class old_converter {
protected:
    pair<expr, constraint_seq> infer_type(old_type_checker & tc, expr const & e);
public:
    virtual ~old_converter() {}
    virtual bool is_opaque(declaration const & d) const = 0;
    virtual optional<declaration> is_delta(expr const & e) const = 0;

    virtual optional<expr> is_stuck(expr const & e, old_type_checker & c) = 0;
    virtual pair<expr, constraint_seq> whnf(expr const & e, old_type_checker & c) = 0;
    virtual pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, old_type_checker & c, delayed_justification & j) = 0;

    pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, old_type_checker & c);
};

/** \brief Old_Converter that allows us to specify constants that should be considered opaque */
template<typename Old_Converter>
class hint_old_converter : public Old_Converter {
    name_predicate m_pred;
public:
    hint_old_converter(environment const & env, name_predicate const & p):Old_Converter(env), m_pred(p) {}
    virtual bool is_opaque(declaration const & d) const { return m_pred(d.get_name()) || Old_Converter::is_opaque(d); }
};

std::unique_ptr<old_converter> mk_dummy_old_converter();

void initialize_old_converter();
void finalize_old_converter();
}
