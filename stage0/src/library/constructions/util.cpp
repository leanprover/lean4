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

extern "C" object * lean_completion_add_to_black_list(object * env, object * n);

environment completion_add_to_black_list(environment const & env, name const & decl_name) {
    return environment(lean_completion_add_to_black_list(env.to_obj_arg(), decl_name.to_obj_arg()));
}

static level get_level(type_checker & ctx, expr const & A) {
    expr S = ctx.whnf(ctx.infer(A));
    if (!is_sort(S))
        throw exception("invalid expression, sort expected");
    return sort_level(S);
}

expr mk_and_intro(type_checker & ctx, expr const & Ha, expr const & Hb) {
    return mk_app(mk_constant(get_and_intro_name()), ctx.infer(Ha), ctx.infer(Hb), Ha, Hb);
}

expr mk_and_left(type_checker &, expr const & H) {
    return mk_proj(get_and_name(), nat(0), H);
}

expr mk_and_right(type_checker &, expr const & H) {
    return mk_proj(get_and_name(), nat(1), H);
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

expr mk_pprod_fst(type_checker &, expr const & p) {
    return mk_proj(get_pprod_name(), nat(0), p);
}

expr mk_pprod_snd(type_checker &, expr const & p) {
    return mk_proj(get_pprod_name(), nat(1), p);
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
    mark_persistent(g_constructions_fresh->raw());
    register_name_generator_prefix(*g_constructions_fresh);
}

void finalize_constructions_util() {
    delete g_constructions_fresh;
}
}
