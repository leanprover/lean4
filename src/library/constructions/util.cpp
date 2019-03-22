/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"
#include "kernel/type_checker.h"
#include "library/util.h"
#include "library/constants.h"

namespace lean {
static name * g_constructions_fresh = nullptr;

static level get_level(type_checker & ctx, expr const & A) {
    expr S = ctx.whnf(ctx.infer(A));
    if (!is_sort(S))
        throw exception("invalid expression, sort expected");
    return sort_level(S);
}

expr mk_and_intro(type_checker & ctx, expr const & Ha, expr const & Hb) {
    return mk_app(mk_constant(get_and_intro_name()), ctx.infer(Ha), ctx.infer(Hb), Ha, Hb);
}

expr mk_and_left(type_checker & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(mk_constant(get_and_left_name()), app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_and_right(type_checker & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(mk_constant(get_and_right_name()), app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_pprod(type_checker & ctx, expr const & A, expr const & B) {
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_pprod_name(), {l1, l2}), A, B);
}

expr mk_pprod_mk(type_checker & ctx, expr const & a, expr const & b) {
    expr A = ctx.infer(a);
    expr B = ctx.infer(b);
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_pprod_mk_name(), {l1, l2}), A, B, a, b);
}

expr mk_pprod_fst(type_checker & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_pprod_fst_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_pprod_snd(type_checker & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_pprod_snd_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_pprod(type_checker & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and(a, b) : mk_pprod(ctx, a, b);
}

expr mk_pprod_mk(type_checker & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and_intro(ctx, a, b) : mk_pprod_mk(ctx, a, b);
}

expr mk_pprod_fst(type_checker & ctx, expr const & p, bool prop) {
    return prop ? mk_and_left(ctx, p) : mk_pprod_fst(ctx, p);
}

expr mk_pprod_snd(type_checker & ctx, expr const & p, bool prop) {
    return prop ? mk_and_right(ctx, p) : mk_pprod_snd(ctx, p);
}

name_generator mk_constructions_name_generator() {
    return name_generator(*g_constructions_fresh);
}

void initialize_constructions_util() {
    g_constructions_fresh = new name("_cnstr_fresh");
    register_name_generator_prefix(*g_constructions_fresh);
}

void finalize_constructions_util() {
    delete g_constructions_fresh;
}
}
