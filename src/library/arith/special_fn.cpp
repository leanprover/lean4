/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "library/hidden_defs.h"
#include "library/arith/special_fn.h"
#include "library/arith/real.h"

namespace lean {
MK_CONSTANT(exp_fn, name("exp"));
MK_CONSTANT(log_fn, name("log"));

MK_CONSTANT(real_pi, name("\u03C0")); // lower case pi
MK_CONSTANT(sin_fn, name("sin"));
MK_CONSTANT(cos_fn, name("cos"));
MK_CONSTANT(tan_fn, name("tan"));
MK_CONSTANT(cot_fn, name("cot"));
MK_CONSTANT(sec_fn, name("sec"));
MK_CONSTANT(csc_fn, name("csc"));

MK_CONSTANT(sinh_fn, name("sinh"));
MK_CONSTANT(cosh_fn, name("cosh"));
MK_CONSTANT(tanh_fn, name("tanh"));
MK_CONSTANT(coth_fn, name("coth"));
MK_CONSTANT(sech_fn, name("sech"));
MK_CONSTANT(csch_fn, name("csch"));

void import_special_fn(environment const & env) {
    if (!env->mark_builtin_imported("special_fn"))
        return;
    import_real(env);

    expr r_r  = Real >> Real;
    expr x    = Const("x");

    env->add_var(exp_fn_name, r_r);
    env->add_var(log_fn_name, r_r);

    env->add_var(real_pi_name, Real);
    env->add_definition(name("pi"), Real, mk_real_pi()); // alias for pi
    env->add_var(sin_fn_name, r_r);
    env->add_definition(cos_fn_name, r_r, Fun({x, Real}, Sin(rSub(x, rDiv(mk_real_pi(), rVal(2))))));
    env->add_definition(tan_fn_name, r_r, Fun({x, Real}, rDiv(Sin(x), Cos(x))));
    env->add_definition(cot_fn_name, r_r, Fun({x, Real}, rDiv(Cos(x), Sin(x))));
    env->add_definition(sec_fn_name, r_r, Fun({x, Real}, rDiv(rVal(1), Cos(x))));
    env->add_definition(csc_fn_name, r_r, Fun({x, Real}, rDiv(rVal(1), Sin(x))));

    env->add_definition(sinh_fn_name, r_r, Fun({x, Real}, rDiv(rSub(rVal(1), Exp(rMul(rVal(-2), x))),
                                                              rMul(rVal(2), Exp(rNeg(x))))));
    env->add_definition(cosh_fn_name, r_r, Fun({x, Real}, rDiv(rAdd(rVal(1), Exp(rMul(rVal(-2), x))),
                                                              rMul(rVal(2), Exp(rNeg(x))))));
    env->add_definition(tanh_fn_name, r_r, Fun({x, Real}, rDiv(Sinh(x), Cosh(x))));
    env->add_definition(coth_fn_name, r_r, Fun({x, Real}, rDiv(Cosh(x), Sinh(x))));
    env->add_definition(sech_fn_name, r_r, Fun({x, Real}, rDiv(rVal(1), Cosh(x))));
    env->add_definition(csch_fn_name, r_r, Fun({x, Real}, rDiv(rVal(1), Sinh(x))));

    for (auto n : {cos_fn_name, tan_fn_name, cot_fn_name, sec_fn_name, csc_fn_name, sinh_fn_name,
                cosh_fn_name, tanh_fn_name, coth_fn_name, sech_fn_name, csch_fn_name}) {
        set_hidden_flag(env, n);
    }
}
}
