/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <utility>
#include "util/optional.h"
#include "util/name.h"
#include "util/rb_map.h"
#include "util/buffer.h"
#include "kernel/environment.h"
#include "library/module.h"
#include "frontends/lean/parser.h"

namespace lean {
struct calc_ext : public environment_extension {
    typedef rb_map<name, std::pair<name, unsigned>, name_quick_cmp> refl_table;
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
    name const & op1 = get_fn_const(arg_types[nargs-1], "invalid calc transitivity rule, last argument must be an operator application");
    name const & op2 = get_fn_const(arg_types[nargs-2], "invalid calc transitivity rule, penultimate argument must be an operator application");
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
    name id = p.check_id_next("invalid 'calc_subst' command, identifier expected");
    return add_calc_subst(p.env(), id);
}

environment calc_refl_cmd(parser & p) {
    name id = p.check_id_next("invalid 'calc_refl' command, identifier expected");
    return add_calc_refl(p.env(), id);
}

environment calc_trans_cmd(parser & p) {
    name id = p.check_id_next("invalid 'calc_trans' command, identifier expected");
    return add_calc_trans(p.env(), id);
}

void register_calc_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("calc_subst",     "set the substitution rule that is used by the calculational proof '{...}' notation", calc_subst_cmd));
    add_cmd(r, cmd_info("calc_refl",      "set the reflexivity rule for an operator, this command is relevant for the calculational proof '{...}' notation", calc_refl_cmd));
    add_cmd(r, cmd_info("calc_trans",     "set the transitivity rule for a pair of operators, this command is relevant for the calculational proof '{...}' notation", calc_trans_cmd));
}
}
