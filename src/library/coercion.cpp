/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/rb_map.h"
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "library/tc_multigraph.h"
#include "library/coercion.h"
#include "library/reducible.h"
#include "library/protected.h"
#include "library/module.h"
#include "library/kernel_serializer.h"
#include "library/scoped_ext.h"
#include "library/pp_options.h"
#include "library/generic_exception.h"

namespace lean {
static name * g_fun  = nullptr;
static name * g_sort = nullptr;

struct coercion_entry {
    name     m_from;
    name     m_coe;
    unsigned m_num_args;
    name     m_to;
    coercion_entry() {}
    coercion_entry(name const & from, name const & coe, unsigned num, name const & to):
        m_from(from), m_coe(coe), m_num_args(num), m_to(to) {}
};

struct coercion_state {
    tc_multigraph                   m_graph;
    name_map<pair<name, unsigned>>  m_coercions; // map coercion -> (from-class, num-args)

    void add1(environment const & env, name const & from, name const & coe, unsigned num, name const & to) {
        m_coercions.insert(coe, mk_pair(from, num));
        m_graph.add1(env, from, coe, to);
    }

    coercion_state():m_graph("coercion") {}
};

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct coercion_config {
    typedef coercion_state  state;
    typedef coercion_entry  entry;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        s.add1(env, e.m_from, e.m_coe, e.m_num_args, e.m_to);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_from << e.m_coe << e.m_num_args << e.m_to;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_from >> e.m_coe >> e.m_num_args >> e.m_to;
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.m_coe.hash());
    }
};

template class scoped_ext<coercion_config>;
typedef scoped_ext<coercion_config> coercion_ext;

void initialize_coercion() {
    name p       = name::mk_internal_unique_name();
    g_fun        = new name(p, "Fun");
    g_sort       = new name(p, "Sort");
    g_class_name = new name("coercions");
    g_key        = new std::string("coerce");
    coercion_ext::initialize();
}

void finalize_coercion() {
    coercion_ext::finalize();
    delete g_key;
    delete g_class_name;
    delete g_fun;
    delete g_sort;
}

optional<pair<name, unsigned>> is_coercion(environment const & env, name const & f) {
    coercion_state const & ext = coercion_ext::get_state(env);
    if (auto it = ext.m_coercions.find(f))
        return optional<pair<name, unsigned>>(*it);
    else
        return optional<pair<name, unsigned>>();
}

optional<pair<name, unsigned>> is_coercion(environment const & env, expr const & f) {
    if (!is_constant(f))
        return optional<pair<name, unsigned>>();
    return is_coercion(env, const_name(f));
}

bool has_coercions_to(environment const & env, name const & D) {
    coercion_state const & ext = coercion_ext::get_state(env);
    return !is_nil(ext.m_graph.get_predecessors(D));
}

bool has_coercions_to_sort(environment const & env) {
    coercion_state const & ext = coercion_ext::get_state(env);
    return !is_nil(ext.m_graph.get_predecessors(*g_sort));
}

bool has_coercions_to_fun(environment const & env) {
    coercion_state const & ext = coercion_ext::get_state(env);
    return !is_nil(ext.m_graph.get_predecessors(*g_fun));
}

bool has_coercions_from(environment const & env, name const & C) {
    coercion_state const & ext = coercion_ext::get_state(env);
    return !is_nil(ext.m_graph.get_successors(C));
}

bool has_coercions_from(environment const & env, expr const & C) {
    expr const & C_fn = get_app_fn(C);
    if (!is_constant(C_fn))
        return false;
    coercion_state const & ext = coercion_ext::get_state(env);
    for (pair<name, name> const & coe_to : ext.m_graph.get_successors(const_name(C_fn))) {
        name const & coe = coe_to.first;
        if (auto it = ext.m_coercions.find(coe)) {
            if (it->second == get_app_num_args(C))
                return true;
        }
    }
    return false;
}

static list<expr> get_coercions_core(environment const & env, expr const & C, name const & D) {
    buffer<expr> args;
    expr const & C_fn = get_app_rev_args(C, args);
    if (!is_constant(C_fn))
        return list<expr>();
    coercion_state const & ext = coercion_ext::get_state(env);
    buffer<expr> r;
    for (pair<name, name> const & coe_to : ext.m_graph.get_successors(const_name(C_fn))) {
        name const & coe = coe_to.first;
        name const & to  = coe_to.second;
        if (to != D)
            continue;
        if (auto it = ext.m_coercions.find(coe)) {
            if (it->second != args.size())
                continue;
        }
        declaration const & coe_decl = env.get(coe);
        if (coe_decl.get_num_univ_params() != length(const_levels(C_fn)))
            continue;
        expr f = mk_constant(coe, const_levels(C_fn));
        r.push_back(mk_rev_app(f, args.size(), args.data()));
    }
    return to_list(r);
}


list<expr> get_coercions(environment const & env, expr const & C, name const & D) {
    return get_coercions_core(env, C, D);
}

list<expr> get_coercions_to_sort(environment const & env, expr const & C) {
    return get_coercions_core(env, C, *g_sort);
}

list<expr> get_coercions_to_fun(environment const & env, expr const & C) {
    return get_coercions_core(env, C, *g_fun);
}

bool get_coercions_from(environment const & env, expr const & C, buffer<expr> & result) {
    buffer<expr> args;
    expr const & C_fn = get_app_rev_args(C, args);
    if (!is_constant(C_fn))
        return false;
    coercion_state const & ext = coercion_ext::get_state(env);
    bool r = false;
    for (pair<name, name> const & coe_to : ext.m_graph.get_successors(const_name(C_fn))) {
        name const & coe = coe_to.first;
        if (auto it = ext.m_coercions.find(coe)) {
            if (it->second != args.size())
                continue;
        }
        declaration const & coe_decl = env.get(coe);
        if (coe_decl.get_num_univ_params() != length(const_levels(C_fn)))
            continue;
        expr f = mk_constant(coe, const_levels(C_fn));
        result.push_back(mk_rev_app(f, args.size(), args.data()));
        r = true;
    }
    return r;
}

void for_each_coercion_user(environment const & env, coercion_user_fn const & f) {
    tc_multigraph const & g = coercion_ext::get_state(env).m_graph;
    g.for_each(f);
}

void for_each_coercion_sort(environment const & env, coercion_sort_fn const & f) {
    tc_multigraph const & g = coercion_ext::get_state(env).m_graph;
    g.for_each([&](name const & from, name const & coe, name const & to) {
            if (to == *g_sort)
                f(from, coe);
        });
}

void for_each_coercion_fun(environment const & env, coercion_fun_fn const & f) {
    tc_multigraph const & g = coercion_ext::get_state(env).m_graph;
    g.for_each([&](name const & from, name const & coe, name const & to) {
            if (to == *g_fun)
                f(from, coe);
        });
}

static void check_pi(name const & f, expr const & t) {
    if (!is_pi(t))
        throw exception(sstream() << "invalid coercion, '" << f << "' is not function");
}

// similar to check_pi, but produces a more informative message
static void check_valid_coercion(name const & f, expr const & t) {
    if (!is_pi(t)) {
        throw_generic_exception(optional<expr>(),[=](formatter const & fmt) {
                options o = fmt.get_options();
                bool show_universes = get_pp_universes(o) || get_pp_all(o);
                std::string ls = show_universes ? ".{ls}" : "";
                std::string us = show_universes ? ".{us}" : "";
                std::string u = show_universes ? ".{u}" : "";
                return format((sstream()
                               << "invalid coercion, type of '" << f
                               << "' does not match any of the acceptable forms "
                               << "for coercions\n"
                               << "coe" << ls << " : Pi (x_1 : A_1) ... (x_n : A_n) (y: C"
                               << ls << " x_1 ... x_n), D" << us << " t_1 ... t_m\n"
                               << "coe" << ls << " : Pi (x_1 : A_1) ... (x_n : A_n) (y: C"
                               << ls << " x_1 ... x_n), Type" << u << "\n"
                               << "coe" << ls << " : Pi (x_1 : A_1) ... (x_n : A_n) (y: C"
                               << ls << " x_1 ... x_n), (Pi x : A, B x)").str());
            });
    }
}

/** \brief Return true iff args contains Var(0), Var(1), ..., Var(args.size() - 1) */
static bool check_var_args(buffer<expr> const & args) {
    for (unsigned i = 0; i < args.size(); i++) {
        if (!is_var(args[i]) || var_idx(args[i]) != i)
            return false;
    }
    return true;
}

/** \brief Return true iff param_id(levels[i]) == level_params[i] */
static bool check_levels(levels ls, level_param_names ps) {
    while (!is_nil(ls) && !is_nil(ps)) {
        if (!is_param(head(ls)))
            return false;
        if (param_id(head(ls)) != head(ps))
            return false;
        ls = tail(ls);
        ps = tail(ps);
    }
    return is_nil(ls) && is_nil(ps);
}

static optional<name> type_to_coercion_class(expr const & t) {
    if (is_sort(t)) {
        return optional<name>(*g_sort);
    } else if (is_pi(t)) {
        return optional<name>(*g_fun);
    } else {
        expr const & C = get_app_fn(t);
        if (is_constant(C))
            return optional<name>(const_name(C));
        else
            return optional<name>();
    }
}

static bool is_user_class(name const & cls) {
    return cls != *g_fun && cls != *g_sort;
}

static unsigned get_num_args(environment const & env, tc_edge const & new_coe) {
    declaration const & d = env.get(new_coe.m_cnst);
    unsigned num = 0;
    buffer<expr> args;
    expr t = d.get_type();
    while (true) {
        if (!is_pi(t))
            return num;
        expr fn = get_app_fn(binding_domain(t));
        if (is_constant(fn) && const_name(fn) == new_coe.m_from)
            return num;
        t = binding_body(t);
        num++;
    }
}

static environment add_coercion_core(environment const & env,
                                     name const & from, name const & coe, unsigned num_args, name const & to,
                                     bool persistent) {
    coercion_state st = coercion_ext::get_state(env);
    pair<environment, list<tc_edge>> new_env_coes = st.m_graph.add(env, from, coe, to);
    environment new_env = new_env_coes.first;
    new_env = coercion_ext::add_entry(new_env, get_dummy_ios(), coercion_entry(from, coe, num_args, to), persistent);
    for (tc_edge const & new_coe : new_env_coes.second) {
        unsigned nargs = get_num_args(new_env, new_coe);
        new_env = coercion_ext::add_entry(new_env, get_dummy_ios(),
                                          coercion_entry(new_coe.m_from, new_coe.m_cnst, nargs, new_coe.m_to), persistent);
        new_env = set_reducible(new_env, new_coe.m_cnst, reducible_status::Reducible, persistent);
        new_env = add_protected(new_env, new_coe.m_cnst);
    }
    return new_env;
}

static environment add_coercion(environment const & env, name const & f, name const & C, bool persistent) {
    declaration d = env.get(f);
    unsigned num = 0;
    buffer<expr> args;
    expr t = d.get_type();
    check_pi(f, t);
    while (true) {
        args.clear();
        expr const & C_fn = get_app_rev_args(binding_domain(t), args);
        if (is_constant(C_fn) &&
            const_name(C_fn) == C &&
            num == args.size() &&
            check_var_args(args) &&
            check_levels(const_levels(C_fn), d.get_univ_params())) {
            optional<name> cls = type_to_coercion_class(binding_body(t));
            if (!cls)
                throw exception(sstream() << "invalid coercion, '" << f << "' cannot be used as a coercion from '"
                                << C << "'");
            else if (is_user_class(*cls) && *cls == C)
                throw exception(sstream() << "invalid coercion, '" << f << "' is a coercion from '" << C << "' to itself");
            return add_coercion_core(env, C, f, num, *cls, persistent);
        }
        t = binding_body(t);
        num++;
        check_valid_coercion(f, t);
    }
}

environment add_coercion(environment const & env, io_state const &, name const & f, bool persistent) {
    declaration d = env.get(f);
    expr t = d.get_type();
    check_pi(f, t);
    buffer<name> Cs; // possible Cs
    while (is_pi(t)) {
        expr d = get_app_fn(binding_domain(t));
        if (is_constant(d))
            Cs.push_back(const_name(d));
        t = binding_body(t);
    }
    if (Cs.empty())
        throw exception(sstream() << "invalid coercion, '" << f << "' cannot be used as a coercion");
    unsigned i = Cs.size();
    while (i > 0) {
        --i;
        if (i == 0) {
            // last alternative
            return add_coercion(env, f, Cs[i], persistent);
        } else {
            try {
                return add_coercion(env, f, Cs[i], persistent);
            } catch (exception &) {
                // failed, keep trying...
            }
        }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}
