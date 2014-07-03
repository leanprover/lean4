/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <string>
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/string.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
typedef std::unordered_map<name, expr_to_tactic_fn, name_hash, name_eq> expr_to_tactic_map;
expr_to_tactic_map & get_expr_to_tactic_map() {
    static expr_to_tactic_map g_map;
    return g_map;
}

void register_expr_to_tactic(name const & n, expr_to_tactic_fn const & fn) {
    get_expr_to_tactic_map().insert(mk_pair(n, fn));
}

tactic expr_to_tactic(type_checker & tc, expr const & e, pos_info_provider const * p) {
    expr const & f = get_app_fn(tc.whnf(e));
    if (is_constant(f)) {
        auto const & map = get_expr_to_tactic_map();
        auto it = map.find(const_name(f));
        if (it != map.end()) {
            return it->second(tc, e, p);
        } else if (auto it = tc.env().find(const_name(f))) {
            if (it->is_definition()) {
                buffer<expr> locals;
                get_app_rev_args(e, locals);
                expr v = it->get_value();
                v = instantiate_univ_params(v, it->get_univ_params(), const_levels(f));
                v = apply_beta(v, locals.size(), locals.data());
                return expr_to_tactic(tc, v, p);
            }
        }
        throw expr_to_tactic_exception(e, "failed to convert expression into tactic");
    } else {
        throw expr_to_tactic_exception(e, "failed to convert expression into tactic");
    }
}

tactic expr_to_tactic(environment const & env, expr const & e, pos_info_provider const * p) {
    type_checker tc(env);
    return expr_to_tactic(tc, e, p);
}

register_simple_tac::register_simple_tac(name const & n, std::function<tactic()> f) {
    register_expr_to_tactic(n, [=](type_checker &, expr const & e, pos_info_provider const *) {
            if (!is_constant(e))
                throw expr_to_tactic_exception(e, "invalid constant tactic");
            return f();
        });
}

register_bin_tac::register_bin_tac(name const & n, std::function<tactic(tactic const &, tactic const &)> f) {
    register_expr_to_tactic(n, [=](type_checker & tc, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 2)
                throw expr_to_tactic_exception(e, "invalid binary tactic, it must have two arguments");
            return f(expr_to_tactic(tc, args[0], p),
                     expr_to_tactic(tc, args[1], p));
        });
}

register_unary_tac::register_unary_tac(name const & n, std::function<tactic(tactic const &)> f) {
    register_expr_to_tactic(n, [=](type_checker & tc, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 1)
                throw expr_to_tactic_exception(e, "invalid unary tactic, it must have one argument");
            return f(expr_to_tactic(tc, args[0], p));
        });
}

static name g_tac("tactic");
static register_simple_tac reg_id(name(g_tac, "id"), []() { return id_tactic(); });
static register_simple_tac reg_now(name(g_tac, "now"), []() { return now_tactic(); });
static register_simple_tac reg_assumption(name(g_tac, "assumption"), []() { return assumption_tactic(); });
static register_simple_tac reg_fail(name(g_tac, "fail"), []() { return fail_tactic(); });
static register_simple_tac reg_beta(name(g_tac, "beta"), []() { return beta_tactic(); });
static register_bin_tac reg_then(name(g_tac, "and_then"), [](tactic const & t1, tactic const & t2) { return then(t1, t2); });
static register_bin_tac reg_orelse(name(g_tac, "or_else"), [](tactic const & t1, tactic const & t2) { return orelse(t1, t2); });
static register_unary_tac reg_repeat(name(g_tac, "repeat"), [](tactic const & t1) { return repeat(t1); });
static register_tac reg_state(name(g_tac, "state"), [](type_checker &, expr const & e, pos_info_provider const * p) {
        if (p)
            return trace_state_tactic(std::string(p->get_file_name()), p->get_pos_info(e));
        else
            return trace_state_tactic("unknown", mk_pair(0, 0));
    });
static register_tac reg_trace(name(g_tac, "trace"), [](type_checker & tc, expr const & e, pos_info_provider const *) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() != 1)
            throw expr_to_tactic_exception(e, "invalid trace tactic, argument expected");
        if (auto str = to_string(args[0]))
            return trace_tactic(*str);
        else if (auto str = to_string(tc.whnf(args[0])))
            return trace_tactic(*str);
        else
            throw expr_to_tactic_exception(e, "invalid trace tactic, string value expected");
    });
static register_tac reg_apply(name(g_tac, "apply"), [](type_checker &, expr const & e, pos_info_provider const *) {
        return apply_tactic(app_arg(e));
    });
static register_tac reg_unfold(name(g_tac, "unfold"), [](type_checker &, expr const & e, pos_info_provider const *) {
        expr id = get_app_fn(app_arg(e));
        if (!is_constant(id))
            return fail_tactic();
        else
            return unfold_tactic(const_name(id));
    });


// We encode the 'by' expression that is used to trigger tactic execution.
// This is a trick to avoid creating a new kind of expression.
// 'by' macros are temporary objects used by the elaborator,
// and have no semantic significance.
[[ noreturn ]] static void throw_ex() { throw exception("unexpected occurrence of 'by' expression"); }
static name g_by_name("by");
class by_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return g_by_name; }
    virtual expr get_type(expr const &, expr const *, extension_context &) const { throw_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_ex(); }
    virtual void write(serializer &) const { throw_ex(); }
};

static macro_definition g_by(new by_macro_cell());
expr mk_by(expr const & e) {
    return mk_macro(g_by, 1, &e);
}

bool is_by(expr const & e) {
    return is_macro(e) && macro_def(e) == g_by;
}

expr const & get_by_arg(expr const & e) {
    lean_assert(is_by(e));
    return macro_arg(e, 0);
}
}
