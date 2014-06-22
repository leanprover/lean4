/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
class type_checker;

class converter {
protected:
    name mk_fresh_name(type_checker & tc);
    expr infer_type(type_checker & tc, expr const & e);
    void add_cnstr(type_checker & tc, constraint const & c);
    extension_context & get_extension(type_checker & tc);
public:
    virtual ~converter() {}
    virtual expr whnf(expr const & e, type_checker & c) = 0;
    virtual bool is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & j) = 0;
    bool is_def_eq(expr const & t, expr const & s, type_checker & c);
};

std::unique_ptr<converter> mk_dummy_converter();
std::unique_ptr<converter> mk_default_converter(environment const & env,
                                                optional<module_idx> mod_idx = optional<module_idx>(),
                                                bool memoize = true,
                                                name_set const & extra_opaque = name_set());
}
