/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/delayed_abstraction.h"
#include "library/metavar_context.h"
#include "library/type_context.h"
using namespace lean;

expr mk_delayed_abstraction(expr const & e, std::initializer_list<pair<expr, expr>> const & as) {
    buffer<name> ns;
    buffer<expr> vs;
    for (auto p : as) {
        ns.push_back(mlocal_name(p.first));
        vs.push_back(p.second);
    }
    return mk_delayed_abstraction(e, ns, vs);
}

#define mkp mk_pair

void tst1() {
    environment env;
    local_context lctx;
    metavar_context mctx;
    expr A  = lctx.mk_local_decl("A", mk_Prop());
    expr a  = lctx.mk_local_decl("a", A);
    expr b  = lctx.mk_local_decl("b", A);
    expr m1 = mctx.mk_metavar_decl(lctx, A);
    lean_assert(is_metavar_decl_ref(m1));
    local_context lctx1;
    expr A1 = lctx1.mk_local_decl("A1", mk_Prop());
    expr a1 = lctx1.mk_local_decl("a1", A1);
    expr b1 = lctx1.mk_local_decl("b1", A1);
    expr e1 = mk_delayed_abstraction(m1, {mkp(A, A1), mkp(a, a1), mkp(b, b1)});
    mctx.assign(m1, a);
    lean_assert(mctx.instantiate_mvars(e1) == a1);
    local_context lctx2;
    expr A2 = lctx2.mk_local_decl("A2", mk_Prop());
    expr a2 = lctx2.mk_local_decl("a2", A2);
    expr b2 = lctx2.mk_local_decl("b2", A2);
    expr e2 = mk_delayed_abstraction(e1, {mkp(A1, A2), mkp(a1, a2), mkp(b1, b2)});
    lean_assert(mctx.instantiate_mvars(e1) == a1);
    lean_assert(mctx.instantiate_mvars(e2) == a2);
    type_context_old ctx(env, options(), mctx, lctx2);
    lean_assert(ctx.infer(e2) == A2);
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_core_module();
    initialize_library_module();
    tst1();
    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
