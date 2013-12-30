/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "library/io_state.h"
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
    io_state ios;
    env->import("specialfn", ios);
}
}
