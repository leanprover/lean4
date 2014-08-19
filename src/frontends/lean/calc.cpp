/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <utility>
#include <algorithm>
#include <vector>
#include "util/optional.h"
#include "util/name.h"
#include "util/rb_map.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "kernel/environment.h"
#include "library/module.h"
#include "library/choice.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"

namespace lean {
struct calc_ext : public environment_extension {
    typedef rb_map<name, pair<name, unsigned>, name_quick_cmp> refl_table;
    typedef rb_map<name_pair, std::tuple<name, name, unsigned>, name_pair_quick_cmp> trans_table;
    optional<name> m_subst;
    unsigned       m_subst_num_args;
    trans_table    m_trans_table;
    refl_table     m_refl_table;
    calc_ext():m_subst_num_args(0) {}
};

struct calc_ext_reg {
    unsigned m_ext_id;
    calc_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<calc_ext>()); }
};

static calc_ext_reg g_ext;
static calc_ext const & get_extension(environment const & env) {
    return static_cast<calc_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, calc_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<calc_ext>(ext));
}

static expr extract_arg_types(environment const & env, name const & f, buffer<expr> & arg_types) {
    expr f_type = env.get(f).get_type();
    while (is_pi(f_type)) {
        arg_types.push_back(binding_domain(f_type));
        f_type = binding_body(f_type);
    }
    return f_type;
}

// Check whether e is of the form (f ...) where f is a constant. If it is return f.
static name const & get_fn_const(expr const & e, char const * msg) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        throw exception(msg);
    return const_name(fn);
}

static std::string g_calc_subst_key("calcs");
static std::string g_calc_refl_key("calcr");
static std::string g_calc_trans_key("calct");

environment add_calc_subst(environment const & env, name const & subst) {
    buffer<expr> arg_types;
    expr r_type = extract_arg_types(env, subst, arg_types);
    unsigned nargs = arg_types.size();
    if (nargs < 2)
        throw exception("invalid calc substitution theorem, it must have at least 2 arguments");
    calc_ext ext = get_extension(env);
    ext.m_subst = subst;
    ext.m_subst_num_args = nargs;
    environment new_env = module::add(env, g_calc_subst_key, [=](serializer & s) {
            s << subst << nargs;
        });
    return update(new_env, ext);
}

environment add_calc_refl(environment const & env, name const & refl) {
    buffer<expr> arg_types;
    expr r_type    = extract_arg_types(env, refl, arg_types);
    unsigned nargs = arg_types.size();
    if (nargs < 1)
        throw exception("invalid calc reflexivity rule, it must have at least 1 argument");
    name const & rop = get_fn_const(r_type, "invalid calc reflexivity rule, result type must be an operator application");
    calc_ext ext = get_extension(env);
    ext.m_refl_table.insert(rop, mk_pair(refl, nargs));
    environment new_env = module::add(env, g_calc_refl_key, [=](serializer & s) {
            s << rop << refl << nargs;
        });
    return update(new_env, ext);
}

environment add_calc_trans(environment const & env, name const & trans) {
    buffer<expr> arg_types;
    expr r_type = extract_arg_types(env, trans, arg_types);
    unsigned nargs = arg_types.size();
    if (nargs < 5)
        throw exception("invalid calc transitivity rule, it must have at least 5 arguments");
    name const & rop = get_fn_const(r_type, "invalid calc transitivity rule, result type must be an operator application");
    name const & op1 = get_fn_const(arg_types[nargs-2], "invalid calc transitivity rule, penultimate argument must be an operator application");
    name const & op2 = get_fn_const(arg_types[nargs-1], "invalid calc transitivity rule, last argument must be an operator application");
    calc_ext ext = get_extension(env);
    ext.m_trans_table.insert(name_pair(op1, op2), std::make_tuple(trans, rop, nargs));
    environment new_env = module::add(env, g_calc_trans_key, [=](serializer & s) {
            s << op1 << op2 << trans << rop << nargs;
        });
    return update(new_env, ext);
}

static void calc_subst_reader(deserializer & d, module_idx, shared_environment &,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> & add_delayed_update) {
    name subst; unsigned nargs;
    d >> subst >> nargs;
    add_delayed_update([=](environment const & env, io_state const &) -> environment {
            calc_ext ext = get_extension(env);
            ext.m_subst = subst;
            ext.m_subst_num_args = nargs;
            return update(env, ext);
        });
}
register_module_object_reader_fn g_calc_subst_reader(g_calc_subst_key, calc_subst_reader);

static void calc_refl_reader(deserializer & d, module_idx, shared_environment &,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> & add_delayed_update) {
    name rop, refl; unsigned nargs;
    d >> rop >> refl >> nargs;
    add_delayed_update([=](environment const & env, io_state const &) -> environment {
            calc_ext ext = get_extension(env);
            ext.m_refl_table.insert(rop, mk_pair(refl, nargs));
            return update(env, ext);
        });
}
register_module_object_reader_fn g_calc_refl_reader(g_calc_refl_key, calc_refl_reader);

static void calc_trans_reader(deserializer & d, module_idx, shared_environment &,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> & add_delayed_update) {
    name op1, op2, trans, rop; unsigned nargs;
    d >> op1 >> op2 >> trans >> rop >> nargs;
    add_delayed_update([=](environment const & env, io_state const &) -> environment {
            calc_ext ext = get_extension(env);
            ext.m_trans_table.insert(name_pair(op1, op2), std::make_tuple(trans, rop, nargs));
            return update(env, ext);
        });
}
register_module_object_reader_fn g_calc_trans_reader(g_calc_trans_key, calc_trans_reader);

environment calc_subst_cmd(parser & p) {
    name id = p.check_constant_next("invalid 'calc_subst' command, constant expected");
    return add_calc_subst(p.env(), id);
}

environment calc_refl_cmd(parser & p) {
    name id = p.check_constant_next("invalid 'calc_refl' command, constant expected");
    return add_calc_refl(p.env(), id);
}

environment calc_trans_cmd(parser & p) {
    name id = p.check_constant_next("invalid 'calc_trans' command, constant expected");
    return add_calc_trans(p.env(), id);
}

void register_calc_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("calc_subst",     "set the substitution rule that is used by the calculational proof '{...}' notation", calc_subst_cmd));
    add_cmd(r, cmd_info("calc_refl",      "set the reflexivity rule for an operator, this command is relevant for the calculational proof '{...}' notation", calc_refl_cmd));
    add_cmd(r, cmd_info("calc_trans",     "set the transitivity rule for a pair of operators, this command is relevant for the calculational proof '{...}' notation", calc_trans_cmd));
}

typedef std::tuple<name, expr, expr>  calc_pred;
typedef pair<calc_pred, expr>         calc_step;
inline name const & pred_op(calc_pred const & p) { return std::get<0>(p); }
inline expr const & pred_lhs(calc_pred const & p) { return std::get<1>(p); }
inline expr const & pred_rhs(calc_pred const & p) { return std::get<2>(p); }
inline calc_pred const & step_pred(calc_step const & s) { return s.first; }
inline expr const & step_proof(calc_step const & s) { return s.second; }
static name g_lcurly("{");
static name g_rcurly("}");
static name g_ellipsis("...");
static name g_colon(":");

static void decode_expr_core(expr const & e, buffer<calc_pred> & preds) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (!is_constant(fn))
        return;
    unsigned nargs = args.size();
    if (nargs < 2)
        return;
    preds.emplace_back(const_name(fn), args[nargs-2], args[nargs-1]);
}

// Check whether e is of the form (f ...) where f is a constant. If it is return f.
static void decode_expr(expr const & e, buffer<calc_pred> & preds, pos_info const & pos) {
    preds.clear();
    if (is_choice(e)) {
        for (unsigned i = 0; i < get_num_choices(e); i++)
            decode_expr_core(get_choice(e, i), preds);
    } else {
        decode_expr_core(e, preds);
    }
    if (preds.empty())
        throw parser_error("invalid 'calc' expression, expression must be a function application 'f a_1 ... a_k' "
                           "where f is a constant, and k >= 2", pos);
}

// Create (op _ _ ... _)
static expr mk_op_fn(parser & p, name const & op, unsigned num_placeholders, pos_info const & pos) {
    expr r = p.save_pos(mk_explicit(mk_constant(op)), pos);
    while (num_placeholders > 0) {
        num_placeholders--;
        r = p.mk_app(r, p.save_pos(mk_expr_placeholder(), pos), pos);
    }
    return r;
}

static void parse_calc_proof(parser & p, buffer<calc_pred> const & preds, std::vector<calc_step> & steps) {
    steps.clear();
    auto pos = p.pos();
    p.check_token_next(g_colon, "invalid 'calc' expression, ':' expected");
    if (p.curr_is_token(g_lcurly)) {
        p.next();
        expr pr = p.parse_expr();
        p.check_token_next(g_rcurly, "invalid 'calc' expression, '}' expected");
        calc_ext const & ext = get_extension(p.env());
        if (!ext.m_subst)
            throw parser_error("invalid 'calc' expression, substitution rule was not defined with calc_subst command", pos);
        for (auto const & pred : preds) {
            auto refl_it = ext.m_refl_table.find(pred_op(pred));
            if (refl_it) {
                expr refl     = mk_op_fn(p, refl_it->first, refl_it->second-1, pos);
                expr refl_pr  = p.mk_app(refl, pred_lhs(pred), pos);
                expr subst    = mk_op_fn(p, *ext.m_subst, ext.m_subst_num_args-2, pos);
                expr subst_pr = p.mk_app({subst, pr, refl_pr}, pos);
                steps.emplace_back(pred, subst_pr);
            }
        }
        if (steps.empty())
            throw parser_error("invalid 'calc' expression, reflexivity rule is not defined for operator", pos);
     } else {
        expr pr = p.parse_expr();
        for (auto const & pred : preds)
            steps.emplace_back(pred, pr);
    }
}

/** \brief Collect distinct rhs's */
static void collect_rhss(std::vector<calc_step> const & steps, buffer<expr> & rhss) {
    rhss.clear();
    for (auto const & step : steps) {
        calc_pred const & pred = step_pred(step);
        expr const & rhs  = pred_rhs(pred);
        if (std::find(rhss.begin(), rhss.end(), rhs) == rhss.end())
            rhss.push_back(rhs);
    }
    lean_assert(!rhss.empty());
}

static void join(parser & p, std::vector<calc_step> const & steps1, std::vector<calc_step> const & steps2, std::vector<calc_step> & res_steps,
                 pos_info const & pos) {
    res_steps.clear();
    calc_ext const & ext = get_extension(p.env());
    for (calc_step const & s1 : steps1) {
        check_interrupted();
        calc_pred const & pred1 = step_pred(s1);
        expr const & pr1        = step_proof(s1);
        for (calc_step const & s2 : steps2) {
            calc_pred const & pred2 = step_pred(s2);
            expr const & pr2        = step_proof(s2);
            if (!is_eqp(pred_rhs(pred1), pred_lhs(pred2)))
                continue;
            auto trans_it = ext.m_trans_table.find(name_pair(pred_op(pred1), pred_op(pred2)));
            if (!trans_it)
                continue;
            expr trans    = mk_op_fn(p, std::get<0>(*trans_it), std::get<2>(*trans_it)-5, pos);
            expr trans_pr = p.mk_app({trans, pred_lhs(pred1), pred_rhs(pred1), pred_rhs(pred2), pr1, pr2}, pos);
            res_steps.emplace_back(calc_pred(std::get<1>(*trans_it), pred_lhs(pred1), pred_rhs(pred2)), trans_pr);
        }
    }
}

expr parse_calc(parser & p) {
    buffer<calc_pred> preds, new_preds;
    buffer<expr>      rhss;
    std::vector<calc_step> steps, new_steps, next_steps;
    auto pos             = p.pos();
    decode_expr(p.parse_expr(), preds, pos);
    parse_calc_proof(p, preds, steps);
    expr dummy     = mk_expr_placeholder();
    while (p.curr_is_token(g_ellipsis)) {
        pos = p.pos();
        p.next();
        decode_expr(p.parse_led(dummy), preds, pos);
        collect_rhss(steps, rhss);
        new_steps.clear();
        for (auto const & pred : preds) {
            if (is_eqp(pred_lhs(pred), dummy)) {
                for (expr const & rhs : rhss)
                    new_preds.emplace_back(pred_op(pred), rhs, pred_rhs(pred));
            }
        }
        if (new_preds.empty())
            throw parser_error("invalid 'calc' expression, invalid expression", pos);
        parse_calc_proof(p, new_preds, new_steps);
        join(p, steps, new_steps, next_steps, pos);
        if (next_steps.empty())
            throw parser_error("invalid 'calc' expression, transitivity rule is not defined for current step", pos);
        steps.swap(next_steps);
    }
    buffer<expr> choices;
    for (auto const & s : steps)
        choices.push_back(step_proof(s));
    return p.save_pos(mk_choice(choices.size(), choices.data()), pos);
}
}
