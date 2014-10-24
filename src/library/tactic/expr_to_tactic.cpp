/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <string>
#include "util/sstream.h"
#include "util/optional.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/annotation.h"
#include "library/string.h"
#include "library/num.h"
#include "library/kernel_serializer.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
static expr * g_and_then_tac_fn   = nullptr;
static expr * g_or_else_tac_fn    = nullptr;
static expr * g_id_tac_fn         = nullptr;
static expr * g_repeat_tac_fn     = nullptr;
static expr * g_determ_tac_fn     = nullptr;
static expr * g_tac_type          = nullptr;
static expr * g_builtin_tac       = nullptr;
static expr * g_fixpoint_tac      = nullptr;
expr const & get_and_then_tac_fn() { return *g_and_then_tac_fn; }
expr const & get_or_else_tac_fn() { return *g_or_else_tac_fn; }
expr const & get_id_tac_fn() { return *g_id_tac_fn; }
expr const & get_determ_tac_fn() { return *g_determ_tac_fn; }
expr const & get_repeat_tac_fn() { return *g_repeat_tac_fn; }
expr const & get_tactic_type() { return *g_tac_type; }
expr const & get_builtin_tac() { return *g_builtin_tac; }

typedef std::unordered_map<name, expr_to_tactic_fn, name_hash, name_eq> expr_to_tactic_map;
static expr_to_tactic_map * g_map = nullptr;

expr_to_tactic_map & get_expr_to_tactic_map() {
    return *g_map;
}

void register_tac(name const & n, expr_to_tactic_fn const & fn) {
    get_expr_to_tactic_map().insert(mk_pair(n, fn));
}

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

static expr * g_tactic_expr_type = nullptr;
static expr * g_tactic_expr_builtin = nullptr;

expr const & get_tactic_expr_type() { return *g_tactic_expr_type; }
expr const & get_tactic_expr_builtin() { return *g_tactic_expr_builtin; }

static name * g_tactic_expr_name = nullptr;
static std::string * g_tactic_expr_opcode = nullptr;

static name * g_tactic_name = nullptr;
static std::string * g_tactic_opcode = nullptr;

name const & get_tactic_expr_name() { return *g_tactic_expr_name; }
std::string const & get_tactic_expr_opcode() { return *g_tactic_expr_opcode; }

name const & get_tactic_name() { return *g_tactic_name; }
std::string const & get_tactic_opcode() { return *g_tactic_opcode; }

class tactic_expr_macro_definition_cell : public macro_definition_cell {
public:
    tactic_expr_macro_definition_cell() {}
    virtual name get_name() const { return get_tactic_expr_name(); }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const {
        return mk_pair(get_tactic_expr_type(), constraint_seq());
    }
    virtual optional<expr> expand(expr const &, extension_context &) const {
        return some_expr(get_tactic_expr_builtin());
    }
    virtual void write(serializer & s) const {
        s.write_string(get_tactic_expr_opcode());
    }
};

static macro_definition * g_tactic_expr_macro = nullptr;

expr mk_tactic_expr(expr const & e) {
    return mk_macro(*g_tactic_expr_macro, 1, &e, e.get_tag());
}

bool is_tactic_expr(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == get_tactic_expr_name();
}

expr const & get_tactic_expr_expr(expr const & e) {
    lean_assert(is_tactic_expr(e));
    return macro_arg(e, 0);
}

void check_tactic_expr(expr const & e, char const * error_msg) {
    if (!is_tactic_expr(e))
        throw expr_to_tactic_exception(e, error_msg);
}

name const & tactic_expr_to_id(expr e, char const * error_msg) {
    if (is_tactic_expr(e))
        e = get_tactic_expr_expr(e);
    if (is_constant(e))
        return const_name(e);
    else if (is_local(e))
        return local_pp_name(e);
    else
        throw expr_to_tactic_exception(e, error_msg);
}

static expr * g_expr_list_cons = nullptr;
static expr * g_expr_list_nil  = nullptr;

void get_tactic_expr_list_elements(expr l, buffer<expr> & r, char const * error_msg) {
    while (true) {
        if (l == *g_expr_list_nil)
            return;
        if (!is_app(l) ||
            !is_app(app_fn(l)) ||
            app_fn(app_fn(l)) != *g_expr_list_cons ||
            !is_tactic_expr(app_arg(app_fn(l))))
            throw expr_to_tactic_exception(l, error_msg);
        r.push_back(get_tactic_expr_expr(app_arg(app_fn(l))));
        l = app_arg(l);
    }
}

void get_tactic_id_list_elements(expr l, buffer<name> & r, char const * error_msg) {
    buffer<expr> es;
    get_tactic_expr_list_elements(l, es, error_msg);
    for (unsigned i = 0; i < es.size(); i++) {
        r.push_back(tactic_expr_to_id(es[i], error_msg));
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

tactic expr_to_tactic(type_checker & tc, elaborate_fn const & fn, expr e, pos_info_provider const * p) {
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
            return it2->second(tc, fn, e, p);
        else
            throw expr_to_tactic_exception(e, sstream() << "implementation for builtin tactic '" <<
                                           const_name(f) << "' was not found");
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
        return expr_to_tactic(tc, fn, v, p);
    }
}

static name * g_tmp_prefix = nullptr;
LEAN_THREAD_VALUE(unsigned, g_expr_tac_id, 0);
static name_generator next_name_generator() {
    unsigned r = g_expr_tac_id;
    g_expr_tac_id++;
    return name_generator(name(*g_tmp_prefix, r));
}

tactic expr_to_tactic(environment const & env, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
    bool memoize             = false;
    type_checker tc(env, next_name_generator(), memoize);
    return expr_to_tactic(tc, fn, e, p);
}

tactic fixpoint(expr const & b, elaborate_fn const & fn) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return expr_to_tactic(env, fn, b, nullptr)(env, ios, s);
        });
}

void register_simple_tac(name const & n, std::function<tactic()> f) {
    register_tac(n, [=](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
            if (!is_constant(e))
                throw expr_to_tactic_exception(e, "invalid constant tactic");
            return f();
        });
}

void register_bin_tac(name const & n, std::function<tactic(tactic const &, tactic const &)> f) {
    register_tac(n, [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 2)
                throw expr_to_tactic_exception(e, "invalid binary tactic, it must have two arguments");
            tactic t1 = expr_to_tactic(tc, fn, args[0], p);
            tactic t2 = expr_to_tactic(tc, fn, args[1], p);
            return f(t1, t2);
        });
}

void register_unary_tac(name const & n, std::function<tactic(tactic const &)> f) {
    register_tac(n, [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 1)
                throw expr_to_tactic_exception(e, "invalid unary tactic, it must have one argument");
            return f(expr_to_tactic(tc, fn, args[0], p));
        });
}

void register_unary_num_tac(name const & n, std::function<tactic(tactic const &, unsigned k)> f) {
    register_tac(n, [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 2)
                throw expr_to_tactic_exception(e, "invalid tactic, it must have two arguments");
            tactic t = expr_to_tactic(tc, fn, args[0], p);
            optional<mpz> k = to_num(args[1]);
            if (!k)
                k = to_num(tc.whnf(args[1]).first);
            if (!k)
                throw expr_to_tactic_exception(e, "invalid tactic, second argument must be a numeral");
            if (!k->is_unsigned_int())
                throw expr_to_tactic_exception(e,
                                               "invalid tactic, second argument does not fit in "
                                               "a machine unsigned integer");
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

    g_tactic_name       = new name("tactic");

    g_tactic_expr_type    = new expr(mk_constant(name(*g_tactic_name, "expr")));
    g_tactic_expr_builtin = new expr(mk_constant(name(const_name(*g_tactic_expr_type), "builtin")));
    g_tactic_expr_name   = new name("tactic-expr");
    g_tactic_expr_opcode = new std::string("TACE");
    g_tactic_expr_macro  = new macro_definition(new tactic_expr_macro_definition_cell());

    register_macro_deserializer(*g_tactic_expr_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_tactic_expr(args[0]);
                                });

    g_expr_list_cons = new expr(mk_constant(name({"tactic", "expr_list", "cons"})));
    g_expr_list_nil  = new expr(mk_constant(name({"tactic", "expr_list", "nil"})));

    name builtin_tac_name(*g_tactic_name, "builtin");
    name and_then_tac_name(*g_tactic_name, "and_then");
    name or_else_tac_name(*g_tactic_name, "or_else");
    name repeat_tac_name(*g_tactic_name, "repeat");
    name fixpoint_name(*g_tactic_name, "fixpoint");
    name determ_tac_name(*g_tactic_name, "determ");
    name id_tac_name(*g_tactic_name, "id");
    g_and_then_tac_fn   = new expr(Const(and_then_tac_name));
    g_or_else_tac_fn    = new expr(Const(or_else_tac_name));
    g_id_tac_fn         = new expr(Const(id_tac_name));
    g_repeat_tac_fn     = new expr(Const(repeat_tac_name));
    g_determ_tac_fn     = new expr(Const(determ_tac_name));
    g_tac_type          = new expr(Const(*g_tactic_name));
    g_builtin_tac       = new expr(Const(builtin_tac_name));
    g_fixpoint_tac      = new expr(Const(fixpoint_name));

    register_simple_tac(id_tac_name,
                        []() { return id_tactic(); });
    register_simple_tac(name(*g_tactic_name, "now"),
                        []() { return now_tactic(); });
    register_simple_tac(name(*g_tactic_name, "assumption"),
                        []() { return assumption_tactic(); });
    register_simple_tac(name(*g_tactic_name, "fail"),
                        []() { return fail_tactic(); });
    register_simple_tac(name(*g_tactic_name, "beta"),
                        []() { return beta_tactic(); });
    register_bin_tac(and_then_tac_name,
                     [](tactic const & t1, tactic const & t2) { return then(t1, t2); });
    register_bin_tac(name(*g_tactic_name, "append"),
                     [](tactic const & t1, tactic const & t2) { return append(t1, t2); });
    register_bin_tac(name(*g_tactic_name, "interleave"),
                     [](tactic const & t1, tactic const & t2) { return interleave(t1, t2); });
    register_bin_tac(name(*g_tactic_name, "par"),
                     [](tactic const & t1, tactic const & t2) { return par(t1, t2); });
    register_bin_tac(or_else_tac_name,
                     [](tactic const & t1, tactic const & t2) { return orelse(t1, t2); });
    register_unary_tac(repeat_tac_name,
                       [](tactic const & t1) { return repeat(t1); });
    register_unary_num_tac(name(*g_tactic_name, "at_most"),
                           [](tactic const & t, unsigned k) { return take(t, k); });
    register_unary_num_tac(name(*g_tactic_name, "discard"),
                           [](tactic const & t, unsigned k) { return discard(t, k); });
    register_unary_num_tac(name(*g_tactic_name, "focus_at"),
                           [](tactic const & t, unsigned k) { return focus(t, k); });
    register_unary_num_tac(name(*g_tactic_name, "try_for"),
                           [](tactic const & t, unsigned k) { return try_for(t, k); });
    register_tac(fixpoint_name,
                 [](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     if (!is_constant(app_fn(e)))
                         throw expr_to_tactic_exception(e, "invalid fixpoint tactic, it must have one argument");
                     expr r = tc.whnf(mk_app(app_arg(e), e)).first;
                     return fixpoint(r, fn);
                 });
}

void finalize_expr_to_tactic() {
    delete g_expr_list_cons;
    delete g_expr_list_nil;
    delete g_tactic_expr_type;
    delete g_tactic_expr_builtin;
    delete g_tactic_expr_name;
    delete g_tactic_expr_opcode;
    delete g_tactic_expr_macro;
    delete g_fixpoint_tac;
    delete g_builtin_tac;
    delete g_tac_type;
    delete g_determ_tac_fn;
    delete g_repeat_tac_fn;
    delete g_or_else_tac_fn;
    delete g_and_then_tac_fn;
    delete g_id_tac_fn;
    delete g_map;
    delete g_tactic_name;
    delete g_tactic_opcode;
    delete g_by_name;
    delete g_tmp_prefix;
}
}
