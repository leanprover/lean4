/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/environment.h"

namespace lean {
class type_checker;

class converter {
protected:
    name mk_fresh_name(type_checker & tc);
    pair<expr, constraint_seq> infer_type(type_checker & tc, expr const & e);
    extension_context & get_extension(type_checker & tc);
public:
    virtual ~converter() {}
    virtual bool is_opaque(declaration const & d) const = 0;
    virtual optional<declaration> is_delta(expr const & e) const = 0;

    virtual bool is_stuck(expr const & e, type_checker & c) = 0;
    virtual pair<expr, constraint_seq> whnf(expr const & e, type_checker & c) = 0;
    virtual pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & j) = 0;

    pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, type_checker & c);
};

std::unique_ptr<converter> mk_dummy_converter();

void initialize_converter();
void finalize_converter();
}
