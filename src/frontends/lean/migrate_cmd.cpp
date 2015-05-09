/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/reducible.h"
#include "library/scoped_ext.h"
#include "library/normalize.h"
#include "library/explicit.h"
#include "library/projection.h"
#include "library/aliases.h"
#include "library/coercion.h"
#include "library/class.h"
#include "library/locals.h"
#include "library/placeholder.h"
#include "library/util.h"
#include "library/occurs.h"
#include "library/module.h"
#include "library/flycheck.h"
#include "library/constants.h"
#include "library/replace_visitor.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tokens.h"

#ifndef LEAN_DEFAULT_MIGRATE_TRACE
#define LEAN_DEFAULT_MIGRATE_TRACE false
#endif

namespace lean {
static name * g_migrate_trace  = nullptr;

bool get_migrate_trace(options const & o) { return o.get_bool(*g_migrate_trace, LEAN_DEFAULT_MIGRATE_TRACE); }

/** \brief Converter used by the migrate command. It treat
    definitions from a given set of namespaces as opaque.
*/
class migrate_converter : public unfold_semireducible_converter {
    list<name> m_namespaces;
public:
    migrate_converter(environment const & env, list<name> const & ns):
        unfold_semireducible_converter(env, true),
        m_namespaces(ns) {
    }

    virtual bool is_opaque(declaration const & d) const {
        name const & n = d.get_name();
        if (!is_instance(m_env, n) &&
            std::any_of(m_namespaces.begin(), m_namespaces.end(), [&](name const & ns) {
                    return is_prefix_of(ns, n);
                }))
            return true;
        return default_converter::is_opaque(d);
    }
};

struct migrate_cmd_fn {
    parser &                 m_p;
    environment              m_env;
    name_generator           m_ngen;
    bool                     m_trace;

    type_checker_ptr         m_tc;
    type_checker_ptr         m_migrate_tc;

    pos_info                 m_pos;
    buffer<expr>             m_params;
    level_param_names        m_ls;
    name                     m_from;
    buffer<pair<name, expr>> m_replacements;
    buffer<pair<name, name>> m_renames;
    buffer<name>             m_hiding;

    bool                     m_throwable; // true if a throwable exception (which is not a lean::exception) was thrown

    list<expr>               m_ctx;
    buffer<expr>             m_S_params;

    migrate_cmd_fn(parser & p):
        m_p(p), m_env(p.env()), m_ngen(p.mk_ngen()) {
        m_throwable = false;
        m_trace     = get_migrate_trace(p.get_options());
    }

    io_state_stream out() const { return regular(m_env, m_p.ios()); }
    expr whnf(expr const & e) { return m_tc->whnf(e).first; }
    expr infer_type(expr const & e) { return m_tc->infer(e).first; }

    /** \brief Return true iff type has at least m_S_params.size() + 1 args, and argument m_S_params.size() is inst_implicit */
    bool check_sufficient_args(expr type) {
        for (unsigned i = 0; i < m_S_params.size(); i++) {
            if (!is_pi(type))
                return false;
            type = binding_body(type);
        }
        return is_pi(type) && binding_info(type).is_inst_implicit();
    }

    /** \brief Return true iff \c e is of the form (p a_1 ... a_n s ...), where
        \c p is a projection, n == m_S_params.size(), and s contains an instance */
    bool is_projection_inst(expr const & e) {
        if (!is_app(e))
            return false;
        expr const & f = get_app_fn(e);
        if (!is_constant(f) || !is_projection(m_env, const_name(f)))
            return false;
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() < m_S_params.size() + 1)
            return false;
        return true; // TODO(Leo): check if instance occurs here refine
    }

    class normalize_fn : public replace_visitor {
        migrate_cmd_fn & m_main;
        unsigned         m_num_params; // number of parameters of the class

        expr visit_app(expr const & e) {
            buffer<expr> args;
            expr f        = get_app_args(e, args);
            expr new_f    = visit(f);
            for (expr & arg : args)
                arg = visit(arg);
            expr r = mk_app(new_f, args);
            if (is_constant(new_f) && args.size() >= m_num_params + 1) {
                name const & fname = const_name(new_f);
                if (is_projection(m_main.m_env, fname)) {
                    return normalize(*m_main.m_migrate_tc, r, true);
                } else {
                    for (auto const & p : m_main.m_replacements) {
                        if (p.first == fname) {
                            expr new_r = p.second;
                            for (unsigned i = m_num_params + 1; i < args.size(); i++)
                                new_r = mk_app(new_r, args[i]);
                            if (m_main.m_tc->is_def_eq(r, new_r).first)
                                return new_r;
                            break;
                        }
                    }
                }
            }
            return r;
        }

        expr visit_binding(expr const & b) {
            expr new_domain = visit(binding_domain(b));
            expr l          = mk_local(m_main.m_tc->mk_fresh_name(), new_domain);
            expr new_body   = abstract(visit(instantiate(binding_body(b), l)), l);
            return update_binding(b, new_domain, new_body);
        }

    public:
        normalize_fn(migrate_cmd_fn & m):
            m_main(m), m_num_params(m_main.m_S_params.size()) {}
    };

    void report_fail_to_migrate(declaration const & d, throwable & ex) {
        if (m_trace) {
            out() << "failed to migrate '" << d.get_name() << "', kernel rejected new declaration\n";
            ::lean::display_error(out(), nullptr, ex);
            out() << "\n";
        }
    }

    void report_skip(declaration const & d, throwable & ex) {
        if (m_trace) {
            out() << "skipped '" << d.get_name() << "': failed to be elaborated\n";
            ::lean::display_error(out(), nullptr, ex);
            out() << "\n";
        }
    }

    void migrate_decl(declaration const & d) {
        if (!check_sufficient_args(d.get_type())) {
            if (m_trace)
                out() << "skipped '" << d.get_name() << "': does not have sufficient number of arguments\n";
            return;
        }
        name d_name = d.get_name();
        if (is_projection(m_env, d_name)) {
            if (m_trace)
                out() << "skipped '" << d.get_name() << "': projections are ignored\n";
            return; // we don't migrate projections
        }
        if (is_coercion(m_env, d_name)) {
            if (m_trace)
                out() << "skipped '" << d.get_name() << "': coercions are ignored\n";
            return; // we don't migrate coercions
        }

        bool renamed = false;
        name short_name, full_name;
        for (auto const & p : m_renames) {
            if (p.first == d_name) {
                renamed    = true;
                full_name  = p.second;
                short_name = full_name.replace_prefix(full_name, name());
                break;
            }
        }
        if (!renamed) {
            short_name = d_name.replace_prefix(m_from, name());
            full_name  = get_namespace(m_env) + short_name;
        }

        if (m_env.find(full_name)) {
            if (m_trace)
                out() << "skipped '" << d.get_name() << "': new name '" << full_name << "' has already been declared\n";
            return; // already has this decl
        }
        try {
            expr d_inst = mk_app(mk_app(mk_explicit(mk_constant(d_name)), m_S_params), mk_strict_expr_placeholder());
            expr v; level_param_names ls;
            std::tie(v, ls) = m_p.elaborate_relaxed(d_inst, m_ctx);
            ls = append(m_ls, ls);
            expr t = normalize_fn(*this)(infer_type(v));

            expr new_type  = Pi(m_params, t);
            expr new_value = Fun(m_params, v);
            try {
                if (d.is_axiom())
                    m_env = module::add(m_env, check(m_env, mk_theorem(m_env, full_name, ls, new_type, new_value)));
                else if (d.is_theorem())
                    m_env = module::add(m_env, check(m_env, mk_theorem(m_env, full_name, ls, new_type, new_value)));
                else
                    m_env = module::add(m_env, check(m_env, mk_definition(m_env, full_name, ls, new_type, new_value)));
                m_p.add_decl_index(full_name, m_pos, d.is_theorem() ? name("theorem") : name("definition"), new_type);
                if (short_name != full_name)
                    m_env = add_expr_alias_rec(m_env, short_name, full_name);
                if (m_trace)
                    out() << "migrated: " << full_name << " : " << new_type << "\n";
            } catch (exception & ex) {
                report_fail_to_migrate(d, ex);
                return;
            } catch (throwable & ex) {
                m_throwable = true;
                report_fail_to_migrate(d, ex);
                return;
            }
        } catch (exception & ex) {
            report_skip(d, ex);
            return;
        } catch (throwable & ex) {
            m_throwable = true;
            report_skip(d, ex);
            return;
        }
    }

    void parse_params() {
        if (!m_p.curr_is_token(get_from_tk())) {
            unsigned rbp = 0;
            m_p.parse_binders(m_params, rbp);
        }
        for (expr const & l : m_params)
            m_p.add_local(l);
    }

    void parse_S_params() {
        m_p.check_token_next(get_with_tk(), "invalid 'migrate' command, 'with' expected");
        while (true) {
            m_S_params.push_back(m_p.parse_expr());
            if (!m_p.curr_is_token(get_comma_tk()))
                break;
            m_p.next();
        }
    }

    void parse_from_namespace() {
        m_p.check_token_next(get_from_tk(), "invalid 'migrate' command, 'from' expected");
        if (!m_p.curr_is_identifier())
            throw parser_error("invalid 'migrate' command, identifier expected", m_p.pos());
        auto n = to_valid_namespace_name(m_env, m_p.get_name_val());
        if (!n)
            throw parser_error(sstream() << "invalid 'migrate' command, '" << m_p.get_name_val() << "' is not a namespace", m_p.pos());
        m_from = *n;
        m_p.next();
    }

    name parse_source_id() {
        if (!m_p.curr_is_identifier())
            throw parser_error("invalid 'migrate' command, identifier expected", m_p.pos());
        name n = m_p.get_name_val();
        if (!m_env.find(n)) {
            n = m_from + n;
            if (!m_env.find(n))
                throw parser_error(sstream() << "invalid 'migrate' command, '" << n << "' is not a declaration", m_p.pos());
        } else {
            if (is_prefix_of(m_from, n))
                throw parser_error(sstream() << "invalid 'migrate' command, '" << n << "' is not in the source namespace", m_p.pos());
        }
        m_p.next();
        return n;
    }

    name parse_to_id() {
        if (!m_p.curr_is_identifier())
            throw parser_error("invalid 'migrate' command, identifier expected", m_p.pos());
        name n = m_p.get_name_val();
        name ns = get_namespace(m_env);
        if (!is_prefix_of(ns, n))
            n = ns + n;
        m_p.next();
        return n;
    }

    void parse_modifiers() {
        while (m_p.curr_is_token(get_replacing_tk()) ||
               m_p.curr_is_token(get_hiding_tk()) ||
               m_p.curr_is_token(get_renaming_tk())) {
            if (m_p.curr_is_token(get_replacing_tk())) {
                m_p.next();
                while (true) {
                    name from_id = parse_source_id();
                    m_p.check_token_next(get_arrow_tk(), "invalid 'migrate' command, '->' expected");
                    expr to   = m_p.parse_expr();
                    m_replacements.emplace_back(from_id, to);
                    if (!m_p.curr_is_token(get_comma_tk()))
                        break;
                    m_p.next();
                }
            } else if (m_p.curr_is_token(get_hiding_tk())) {
                m_p.next();
                while (true) {
                    name id = parse_source_id();
                    m_hiding.push_back(id);
                    if (!m_p.curr_is_token(get_comma_tk()))
                        break;
                    m_p.next();
                }
            } else if (m_p.curr_is_token(get_renaming_tk())) {
                m_p.next();
                name from_id = parse_source_id();
                m_p.check_token_next(get_arrow_tk(), "invalid 'migrate' command, '->' expected");
                name to_id   = parse_to_id();
                m_renames.emplace_back(from_id, to_id);
                if (!m_p.curr_is_token(get_comma_tk()))
                    break;
                m_p.next();
            } else {
                lean_unreachable();
            }
        }
    }

    expr update_locals(expr new_tmp, buffer<expr> & locals) {
        for (unsigned i = 0; i < locals.size(); i++) {
            expr new_local = mk_local(mlocal_name(locals[i]), binding_name(new_tmp), binding_domain(new_tmp),
                                      binding_info(new_tmp));
            locals[i]      = new_local;
            new_tmp        = instantiate(binding_body(new_tmp), new_local);
        }
        return new_tmp;
    }

    // hack to treat expressions as type
    expr mk_as_type(expr const & e) {
        return mk_app(mk_constant(get_eq_name()), e, e);
    }

    expr get_as_type_expr(expr const & e) {
        lean_assert(is_eq(e));
        return app_arg(e);
    }

    void elaborate() {
        buffer<expr> include_vars;
        m_p.get_include_variables(include_vars);
        buffer<expr> tmp_locals;
        tmp_locals.append(m_params);
        for (auto const & p : m_S_params)
            tmp_locals.push_back(mk_local(m_ngen.next(), mk_as_type(p)));
        for (auto const & p : m_replacements)
            tmp_locals.push_back(mk_local(m_ngen.next(), mk_as_type(p.second)));

        expr_struct_set dep_set;
        for (expr const & v : include_vars) {
            ::lean::collect_locals(mlocal_type(v), dep_set);
            dep_set.insert(v);
        }
        for (expr const & p : m_params)
            ::lean::collect_locals(mlocal_type(p), dep_set);
        buffer<expr> ctx;
        sort_locals(dep_set, m_p, ctx);
        expr dummy     = mk_Prop();
        expr tmp       = Pi_as_is(ctx, Pi(tmp_locals, dummy, m_p), m_p);

        level_param_names new_ls;
        expr new_tmp;
        std::tie(new_tmp, new_ls) = m_p.elaborate_type(tmp, list<expr>());
        m_ls    = new_ls;
        new_tmp = update_locals(new_tmp, ctx);
        new_tmp = update_locals(new_tmp, m_params);
        for (auto & p : m_S_params) {
            p        = get_as_type_expr(binding_domain(new_tmp));
            new_tmp  = binding_body(new_tmp);
        }
        for (auto & p : m_replacements) {
            p.second = get_as_type_expr(binding_domain(new_tmp));
            new_tmp  = binding_body(new_tmp);
        }

        buffer<expr> explicit_params;
        explicit_params.append(m_params);
        m_params.clear();
        m_params.append(ctx);
        m_params.append(explicit_params);
    }

    environment operator()() {
        m_pos = m_p.pos();

        m_migrate_tc = std::unique_ptr<type_checker>(new type_checker(m_env, m_ngen.mk_child(),
                       std::unique_ptr<converter>(new migrate_converter(m_env, get_namespaces(m_env)))));
        m_tc = std::unique_ptr<type_checker>(new type_checker(m_env, m_ngen.mk_child(),
               std::unique_ptr<converter>(new unfold_semireducible_converter(m_env, true))));

        parse_params();
        parse_from_namespace();
        parse_S_params();
        parse_modifiers();
        elaborate();

        m_ctx = reverse_to_list(m_params.begin(), m_params.end());

        for (expr & p : m_S_params)
            p = mk_as_is(p);

        environment env = m_env;
        env.for_each_declaration([&](declaration const & d) {
                if (!d.is_definition() && !d.is_theorem() && !d.is_axiom())
                    return;
                if (std::find(m_hiding.begin(), m_hiding.end(), d.get_name()) != m_hiding.end())
                    return;
                if (is_prefix_of(m_from, d.get_name()))
                    migrate_decl(d);
            });
        if (m_throwable && !m_trace) {
            flycheck_warning wrn(m_p.regular_stream());
            m_p.display_warning_pos(m_pos);
            m_p.regular_stream() << " some declarations were not migrated due to resource constraints (use 'set_option migrate.trace true' for additional details)" << endl;
        }
        return m_env;
    }
};

static environment migrate_cmd(parser & p) {
    return migrate_cmd_fn(p)();
}

void register_migrate_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("migrate",   "instantiate structure theorems", migrate_cmd));
}

void initialize_migrate_cmd() {
    g_migrate_trace = new name{"migrate", "trace"};
    register_bool_option(*g_migrate_trace, LEAN_DEFAULT_MIGRATE_TRACE,
                         "(migrate) enable/disable trace messages describing which declarations have been migrated");
}

void finalize_migrate_cmd() {
    delete g_migrate_trace;
}
}
