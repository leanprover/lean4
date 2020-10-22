/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/

#include "library/abstract_type_context.h"
#include "library/type_context.h"
#include "library/formatter.h"
#include "util/io.h"

namespace lean {
extern "C" object * lean_pp_expr(object * env, object * mctx, object * lctx, object * opts, object * e, object * w);

formatter_factory mk_pretty_formatter_factory() {
    return [](environment const & env, options const & o, abstract_type_context & ctx) { // NOLINT
        return formatter(o, [&](expr const & e, options const & new_o) {
            // what could ever go wrong
            return get_io_result<format>(lean_pp_expr(env.to_obj_arg(), ctx.mctx().to_obj_arg(), ctx.lctx().to_obj_arg(), new_o.to_obj_arg(), e.to_obj_arg(), box(0)));
        });
    };
}

void initialize_pp() {}
void finalize_pp() {}
}
