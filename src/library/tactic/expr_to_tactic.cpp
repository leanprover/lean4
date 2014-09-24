/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <string>
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/annotation.h"
#include "library/string.h"
#include "library/num.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
typedef std::unordered_map<name, expr_to_tactic_fn, name_hash, name_eq> expr_to_tactic_map;
static expr_to_tactic_map * g_map = nullptr;

expr_to_tactic_map & get_expr_to_tactic_map() {
    return *g_map;
}

void register_tac(name const & n, expr_to_tactic_fn const & fn) {
    get_expr_to_tactic_map().insert(mk_pair(n, fn));
}

static expr * g_exact_tac_fn      = nullptr;
static expr * g_and_then_tac_fn   = nullptr;
static expr * g_or_else_tac_fn    = nullptr;
static expr * g_repeat_tac_fn     = nullptr;
static expr * g_determ_tac_fn     = nullptr;
static expr * g_tac_type          = nullptr;
static expr * g_builtin_tac       = nullptr;
static expr * g_fixpoint_tac      = nullptr;
expr const & get_exact_tac_fn() { return *g_exact_tac_fn; }
expr const & get_and_then_tac_fn() { return *g_and_then_tac_fn; }
expr const & get_or_else_tac_fn() { return *g_or_else_tac_fn; }
expr const & get_determ_tac_fn() { return *g_determ_tac_fn; }
expr const & get_repeat_tac_fn() { return *g_repeat_tac_fn; }
expr const & get_tactic_type() { return *g_tac_type; }

bool has_tactic_decls(environment const & env) {
    try {
        type_checker tc(env);
        return
            tc.infer(*g_builtin_tac).first     == *g_tac_type &&
            tc.infer(*g_and_then_tac_fn).first == *g_tac_type >> (*g_tac_type >> *g_tac_type) &&
            tc.infer(*g_or_else_tac_fn).first  == *g_tac_type >> (*g_tac_type >> *g_tac_type) &&
            tc.infer(*g_repeat_tac_fn).first   == *g_tac_type >> *g_tac_type;
    } catch (exception &) {
        return false;
    }
}

static void throw_failed(expr const & e) {
    throw expr_to_tactic_exception(e, "failed to convert expression into tactic");
}

/** \brief Return true if v is the constant tactic.builtin or the constant function that returns tactic.builtin_tactic */
static bool is_builtin_tactic(expr const & v) {
    if (is_lambda(v))
        return is_builtin_tactic(binding_body(v));
    else if (v == *g_builtin_tac)
        return true;
    else
        return false;
}

tactic expr_to_tactic(type_checker & tc, expr e, pos_info_provider const * p) {
    e = tc.whnf(e).first;
    expr f = get_app_fn(e);
    if (!is_constant(f))
        throw_failed(e);
    optional<declaration> it = tc.env().find(const_name(f));
    if (!it || !it->is_definition())
        throw_failed(e);
    expr v = it->get_value();
    if (is_builtin_tactic(v)) {
        auto const & map = get_expr_to_tactic_map();
        auto it2 = map.find(const_name(f));
        if (it2 != map.end())
            return it2->second(tc, e, p);
        else
            throw expr_to_tactic_exception(e, sstream() << "implementation for builtin tactic '" << const_name(f) << "' was not found");
    } else {
        // unfold definition
        buffer<expr> locals;
        get_app_rev_args(e, locals);
        level_param_names const & ps = it->get_univ_params();
        levels ls = const_levels(f);
        unsigned num_ps = length(ps);
        unsigned num_ls = length(ls);
        if (num_ls > num_ps)
            throw expr_to_tactic_exception(e, sstream() << "invalid number of universes");
        if (num_ls < num_ps) {
            buffer<level> extra_ls;
            name_generator ngen = tc.mk_ngen();
            for (unsigned i = num_ls; i < num_ps; i++)
                extra_ls.push_back(mk_meta_univ(ngen.next()));
            ls = append(ls, to_list(extra_ls.begin(), extra_ls.end()));
        }
        v = instantiate_univ_params(v, ps, ls);
        v = apply_beta(v, locals.size(), locals.data());
        return expr_to_tactic(tc, v, p);
    }
}

static name * g_tmp_prefix = nullptr;
LEAN_THREAD_VALUE(unsigned, g_expr_tac_id, 0);
static name_generator next_name_generator() {
    unsigned r = g_expr_tac_id;
    g_expr_tac_id++;
    return name_generator(name(*g_tmp_prefix, r));
}

tactic expr_to_tactic(environment const & env, expr const & e, pos_info_provider const * p) {
    type_checker tc(env, next_name_generator());
    return expr_to_tactic(tc, e, p);
}

tactic fixpoint(expr const & b) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return expr_to_tactic(env, b, nullptr)(env, ios, s);
        });
}

void register_simple_tac(name const & n, std::function<tactic()> f) {
    register_tac(n, [=](type_checker &, expr const & e, pos_info_provider const *) {
            if (!is_constant(e))
                throw expr_to_tactic_exception(e, "invalid constant tactic");
            return f();
        });
}

void register_bin_tac(name const & n, std::function<tactic(tactic const &, tactic const &)> f) {
    register_tac(n, [=](type_checker & tc, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 2)
                throw expr_to_tactic_exception(e, "invalid binary tactic, it must have two arguments");
            return f(expr_to_tactic(tc, args[0], p),
                     expr_to_tactic(tc, args[1], p));
        });
}

void register_unary_tac(name const & n, std::function<tactic(tactic const &)> f) {
    register_tac(n, [=](type_checker & tc, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 1)
                throw expr_to_tactic_exception(e, "invalid unary tactic, it must have one argument");
            return f(expr_to_tactic(tc, args[0], p));
        });
}

void register_unary_num_tac(name const & n, std::function<tactic(tactic const &, unsigned k)> f) {
    register_tac(n, [=](type_checker & tc, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 2)
                throw expr_to_tactic_exception(e, "invalid tactic, it must have two arguments");
            tactic t = expr_to_tactic(tc, args[0], p);
            optional<mpz> k = to_num(args[1]);
            if (!k)
                k = to_num(tc.whnf(args[1]).first);
            if (!k)
                throw expr_to_tactic_exception(e, "invalid tactic, second argument must be a numeral");
            if (!k->is_unsigned_int())
                throw expr_to_tactic_exception(e, "invalid tactic, second argument does not fit in a machine unsigned integer");
            return f(t, k->get_unsigned_int());
        });
}

static name * g_by_name = nullptr;

expr mk_by(expr const & e) { return mk_annotation(*g_by_name, e); }
bool is_by(expr const & e) { return is_annotation(e, *g_by_name); }
expr const & get_by_arg(expr const & e) { lean_assert(is_by(e)); return get_annotation_arg(e); }

void initialize_expr_to_tactic() {
    g_tmp_prefix        = new name(name::mk_internal_unique_name());

    g_by_name           = new name("by");
    register_annotation(*g_by_name);

    g_map               = new expr_to_tactic_map();

    name g_tac("tactic");
    name g_builtin_tac_name(g_tac, "builtin");
    name g_exact_tac_name(g_tac, "exact");
    name g_and_then_tac_name(g_tac, "and_then");
    name g_or_else_tac_name(g_tac, "or_else");
    name g_repeat_tac_name(g_tac, "repeat");
    name g_fixpoint_name(g_tac, "fixpoint");
    name g_determ_tac_name(g_tac, "determ");
    g_exact_tac_fn      = new expr(Const(g_exact_tac_name));
    g_and_then_tac_fn   = new expr(Const(g_and_then_tac_name));
    g_or_else_tac_fn    = new expr(Const(g_or_else_tac_name));
    g_repeat_tac_fn     = new expr(Const(g_repeat_tac_name));
    g_determ_tac_fn     = new expr(Const(g_determ_tac_name));
    g_tac_type          = new expr(Const(g_tac));
    g_builtin_tac       = new expr(Const(g_builtin_tac_name));
    g_fixpoint_tac      = new expr(Const(g_fixpoint_name));

    register_simple_tac(name(g_tac, "id"), []() { return id_tactic(); });
    register_simple_tac(name(g_tac, "now"), []() { return now_tactic(); });
    register_simple_tac(name(g_tac, "assumption"), []() { return assumption_tactic(); });
    register_simple_tac(name(g_tac, "eassumption"), []() { return eassumption_tactic(); });
    register_simple_tac(name(g_tac, "fail"), []() { return fail_tactic(); });
    register_simple_tac(name(g_tac, "beta"), []() { return beta_tactic(); });
    register_bin_tac(g_and_then_tac_name, [](tactic const & t1, tactic const & t2) { return then(t1, t2); });
    register_bin_tac(name(g_tac, "append"), [](tactic const & t1, tactic const & t2) { return append(t1, t2); });
    register_bin_tac(name(g_tac, "interleave"), [](tactic const & t1, tactic const & t2) { return interleave(t1, t2); });
    register_bin_tac(name(g_tac, "par"), [](tactic const & t1, tactic const & t2) { return par(t1, t2); });
    register_bin_tac(g_or_else_tac_name, [](tactic const & t1, tactic const & t2) { return orelse(t1, t2); });
    register_unary_tac(g_repeat_tac_name, [](tactic const & t1) { return repeat(t1); });
    register_tac(name(g_tac, "state"), [](type_checker &, expr const & e, pos_info_provider const * p) {
            if (p)
                if (auto it = p->get_pos_info(e))
                    return trace_state_tactic(std::string(p->get_file_name()), *it);
            return trace_state_tactic();
        });
    register_tac(name(g_tac, "trace"), [](type_checker & tc, expr const & e, pos_info_provider const *) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 1)
                throw expr_to_tactic_exception(e, "invalid trace tactic, argument expected");
            if (auto str = to_string(args[0]))
                return trace_tactic(*str);
            else if (auto str = to_string(tc.whnf(args[0]).first))
                return trace_tactic(*str);
            else
                throw expr_to_tactic_exception(e, "invalid trace tactic, string value expected");
        });
    register_tac(name(g_tac, "apply"), [](type_checker &, expr const & e, pos_info_provider const *) {
            return apply_tactic(app_arg(e));
        });
    register_tac(g_exact_tac_name, [](type_checker &, expr const & e, pos_info_provider const *) {
            return exact_tactic(app_arg(e));
        });
    register_tac(name(g_tac, "unfold"), [](type_checker &, expr const & e, pos_info_provider const *) {
            expr id = get_app_fn(app_arg(e));
            if (!is_constant(id))
                return fail_tactic();
            else
                return unfold_tactic(const_name(id));
        });
    register_unary_num_tac(name(g_tac, "at_most"), [](tactic const & t, unsigned k) { return take(t, k); });
    register_unary_num_tac(name(g_tac, "discard"), [](tactic const & t, unsigned k) { return discard(t, k); });
    register_unary_num_tac(name(g_tac, "focus_at"), [](tactic const & t, unsigned k) { return focus(t, k); });
    register_unary_num_tac(name(g_tac, "try_for"), [](tactic const & t, unsigned k) { return try_for(t, k); });
    register_tac(g_fixpoint_name, [](type_checker & tc, expr const & e, pos_info_provider const *) {
            if (!is_constant(app_fn(e)))
                throw expr_to_tactic_exception(e, "invalid fixpoint tactic, it must have one argument");
            expr r = tc.whnf(mk_app(app_arg(e), e)).first;
            return fixpoint(r);
        });
}

void finalize_expr_to_tactic() {
    delete g_fixpoint_tac;
    delete g_builtin_tac;
    delete g_tac_type;
    delete g_determ_tac_fn;
    delete g_repeat_tac_fn;
    delete g_or_else_tac_fn;
    delete g_and_then_tac_fn;
    delete g_exact_tac_fn;
    delete g_map;
    delete g_by_name;
    delete g_tmp_prefix;
}
}
