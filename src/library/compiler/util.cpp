/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/find_fn.h"
#include "kernel/old_type_checker.h"
#include "library/aux_recursors.h"
#include "library/util.h"
#include "library/vm/vm.h"
#include "library/type_context.h"

namespace lean {
name mk_compiler_unused_name(environment const & env, name const & prefix, char const * suffix, unsigned & idx) {
    while (true) {
        name curr(prefix, suffix);
        curr = curr.append_after(idx);
        idx++;
        if (!env.find(curr) && !is_vm_function(env, curr))
            return curr;
    }
}

bool is_comp_irrelevant(type_context_old & ctx, expr const & e) {
    expr type = ctx.whnf(ctx.infer(e));
    return is_sort(type) || ctx.is_prop(type);
}

bool is_cases_on_recursor(environment const & env, name const & n) {
    return ::lean::is_aux_recursor(env, n) && n.get_string() == "cases_on";
}

unsigned get_constructor_arity(environment const & env, name const & n) {
    constant_info info = env.get(n);
    expr e = info.get_type();
    unsigned r = 0;
    while (is_pi(e)) {
        r++;
        e = binding_body(e);
    }
    return r;
}
}
