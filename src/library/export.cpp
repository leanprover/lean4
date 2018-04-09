/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include "frontends/lean/parser_config.h"
#include "kernel/quotient/quotient.h"
#include "kernel/expr_maps.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/module.h"
#include "library/unfold_macros.h"

namespace lean {
template<typename T>
using level_map = typename std::unordered_map<level, T, level_hash, level_eq>;

template<typename T>
using name_hmap = typename std::unordered_map<name, T, name_hash, name_eq>;


class exporter {
    std::ostream &               m_out;
    environment                  m_env;
    std::unordered_set<name, name_hash> m_exported;
    name_hmap<unsigned>          m_name2idx;
    level_map<unsigned>          m_level2idx;
    expr_bi_map<unsigned>        m_expr2idx;
    bool                         m_quotient_exported = false;

    unsigned export_name(name const & n) {
        auto it = m_name2idx.find(n);
        if (it != m_name2idx.end())
            return it->second;
        unsigned i;
        if (n.is_anonymous()) {
            lean_unreachable();
        } else if (n.is_string()) {
            unsigned p = export_name(n.get_prefix());
            i = static_cast<unsigned>(m_name2idx.size());
            m_out << i << " #NS " << p << " " << n.get_string() << "\n";
        } else {
            unsigned p = export_name(n.get_prefix());
            i = static_cast<unsigned>(m_name2idx.size());
            m_out << i << " #NI " << p << " " << n.get_numeral() << "\n";
        }
        m_name2idx[n] = i;
        return i;
    }

    unsigned export_level(level const & l) {
        auto it = m_level2idx.find(l);
        if (it != m_level2idx.end())
            return it->second;
        unsigned i = 0;
        unsigned l1, l2, n;
        switch (l.kind()) {
        case level_kind::Zero:
            lean_unreachable();
            break;
        case level_kind::Succ:
            l1 = export_level(succ_of(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #US " << l1 << "\n";
            break;
        case level_kind::Max:
            l1 = export_level(max_lhs(l));
            l2 = export_level(max_rhs(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #UM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::IMax:
            l1 = export_level(imax_lhs(l));
            l2 = export_level(imax_rhs(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #UIM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::Param:
            n = export_name(param_id(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #UP " << n << "\n";
            break;
        case level_kind::Meta:
            throw exception("invalid 'export', universe meta-variables cannot be exported");
        }
        m_level2idx[l] = i;
        return i;
    }

    void display_binder_info(binder_info const & bi) {
        if (bi.is_implicit())
            m_out << "#BI";
        else if (bi.is_strict_implicit())
            m_out << "#BS";
        else if (bi.is_inst_implicit())
            m_out << "#BC";
        else
            m_out << "#BD";
    }

    unsigned export_binding(expr const & e, char const * k) {
        unsigned n  = export_name(binding_name(e));
        unsigned e1 = export_expr(binding_domain(e));
        unsigned e2 = export_expr(binding_body(e));
        unsigned i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " " << k << " ";
        display_binder_info(binding_info(e));
        m_out << " " << n << " " << e1 << " " << e2 << "\n";
        return i;
    }

    unsigned export_const(expr const & e) {
        buffer<unsigned> ls;
        unsigned n = export_name(const_name(e));
        for (level const & l : const_levels(e))
            ls.push_back(export_level(l));
        unsigned i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " #EC " << n;
        for (unsigned l : ls)
            m_out << " " << l;
        m_out << "\n";
        return i;
    }

    unsigned export_expr(expr const & e) {
        auto it = m_expr2idx.find(e);
        if (it != m_expr2idx.end())
            return it->second;
        unsigned i = 0;
        unsigned l, e1, e2;
        switch (e.kind()) {
        case expr_kind::Var:
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #EV " << var_idx(e) << "\n";
            break;
        case expr_kind::Sort:
            l = export_level(sort_level(e));
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #ES " << l << "\n";
            break;
        case expr_kind::Constant:
            i = export_const(e);
            break;
        case expr_kind::App:
            e1 = export_expr(app_fn(e));
            e2 = export_expr(app_arg(e));
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #EA " << e1 << " " << e2 << "\n";
            break;
        case expr_kind::Let: {
            auto n = export_name(let_name(e));
            e1 = export_expr(let_type(e));
            e2 = export_expr(let_value(e));
            auto e3 = export_expr(let_body(e));
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #EZ " << n << " " << e1 << " " << e2 << " " << e3 << "\n";
            break;
        }
        case expr_kind::Lambda:
            i = export_binding(e, "#EL");
            break;
        case expr_kind::Pi:
            i = export_binding(e, "#EP");
            break;
        case expr_kind::Meta:
            throw exception("invalid 'export', meta-variables cannot be exported");
        case expr_kind::Local:
            throw exception("invalid 'export', local constants cannot be exported");
        case expr_kind::Macro:
            throw exception("invalid 'export', macros cannot be exported");
        }
        m_expr2idx[e] = i;
        return i;
    }

    void export_dependencies(expr const & e) {
        for_each(e, [&](expr const & c, unsigned) {
                if (is_constant(c))
                    export_declaration(const_name(c));
                return true;
            });
    }

    void export_definition(declaration const & d) {
        unsigned n = export_name(d.get_name());
        export_dependencies(d.get_type());
        export_dependencies(d.get_value());
        auto ps = map2<unsigned>(d.get_univ_params(), [&] (name const & p) { return export_name(p); });
        auto t = export_expr(d.get_type());
        auto v = export_expr(d.get_value());
        m_out << "#DEF " << n << " " << t << " " << v;
        for (unsigned p : ps)
            m_out << " " << p;
        m_out << "\n";
    }

    void export_axiom(declaration const & d) {
        unsigned n = export_name(d.get_name());
        export_dependencies(d.get_type());
        auto ps = map2<unsigned>(d.get_univ_params(), [&] (name const & p) { return export_name(p); });
        auto t = export_expr(d.get_type());
        m_out << "#AX " << n << " " << t;
        for (unsigned p : ps)
            m_out << " " << p;
        m_out << "\n";
    }

    void export_declaration(name const & n) {
        if (!m_exported.count(n))
            export_declaration(m_env.get(n));
    }

    void export_declaration(declaration d) {
        // do not export meta declarations
        if (!d.is_trusted()) return;

        if (is_quotient_decl(m_env, d.get_name()))
            return export_quotient();
        if (inductive::is_inductive_decl(m_env, d.get_name()))
            return export_inductive(d.get_name());
        if (auto ind_type = inductive::is_intro_rule(m_env, d.get_name()))
            return export_inductive(*ind_type);
        if (auto ind_type = inductive::is_elim_rule(m_env, d.get_name()))
            return export_inductive(*ind_type);

        if (m_exported.count(d.get_name())) return;
        m_exported.insert(d.get_name());

        d = unfold_all_macros(m_env, d);

        if (d.is_definition()) {
            return export_definition(d);
        } else {
            return export_axiom(d);
        }
    }

    void export_inductive(name const & n) {
        if (m_exported.count(n)) return;
        m_exported.insert(n);

        auto decl = *inductive::is_inductive_decl(m_env, n);
        decl.m_type = unfold_all_macros(m_env, decl.m_type);
        decl.m_intro_rules = map(decl.m_intro_rules,
                                 [&] (inductive::intro_rule const & i) {
                                     return unfold_all_macros(m_env, i);
                                 });

        export_dependencies(decl.m_type);
        for (auto & c : decl.m_intro_rules)
            export_dependencies(c);

        for (auto & p : decl.m_level_params)
            export_name(p);
        export_name(decl.m_name);
        export_expr(decl.m_type);
        for (auto & c : decl.m_intro_rules) {
            export_name(inductive::intro_rule_name(c));
            export_expr(inductive::intro_rule_type(c));
        }

        m_out << "#IND " << decl.m_num_params << " "
              << export_name(decl.m_name) << " "
              << export_expr(decl.m_type) << " "
              << length(decl.m_intro_rules);
        for (auto & c : decl.m_intro_rules) {
            // intro rules are stored as local constants, we split them up so that
            // the type checkers do not need to implement local constants.
            m_out << " " << export_name(inductive::intro_rule_name(c))
                  << " " << export_expr(inductive::intro_rule_type(c));
        }
        for (name const & p : decl.m_level_params)
            m_out << " " << export_name(p);
        m_out << "\n";
    }

    void export_declarations() {
        m_env.for_each_declaration([&] (declaration const & d) {
                export_declaration(d);
            });
    }

    void export_quotient() {
        if (m_quotient_exported) return;
        m_quotient_exported = true;

        for (auto & n : quotient_required_decls())
            export_declaration(n);

        m_out << "#QUOT\n";
    }

    void export_notation(notation_entry const & entry) {
        if (entry.parse_only()) return;
        if (length(entry.get_transitions()) != 1) return;
        auto & t = head(entry.get_transitions());

        buffer<expr> args;
        auto & fn = get_app_rev_args(entry.get_expr(), args);

        char const * type = nullptr;
        if (args.size() == 1 && args[0] == mk_var(0)) {
            if (entry.is_nud()) {
                type = "#PREFIX";
            } else {
                type = "#POSTFIX";
            }
        } else if (!entry.is_nud() && args.size() == 2 && args[0] == mk_var(0) && args[1] == mk_var(1)) {
            type = "#INFIX";
        }

        if (type && is_constant(fn)) {
            auto fni = export_name(const_name(fn));
            auto prec_opt = get_expr_precedence(get_token_table(m_env), t.get_token().get_string());
            auto prec = prec_opt ? *prec_opt : 0;
            m_out << type << " " << fni << " " << prec << " " << t.get_pp_token().get_string() << "\n";
        }
    }

    void export_notation() {
        for (auto & entry : get_notation_entries(m_env)) {
            export_notation(entry);
        }
    }

public:
    exporter(std::ostream & out, environment const & env) : m_out(out), m_env(env) {}

    void operator()(optional<list<name>> const & decls) {
        m_name2idx[{}] = 0;
        m_level2idx[{}] = 0;
        if (has_quotient(m_env))
            export_quotient();
        if (decls) {
            for (auto & d : *decls)
                export_declaration(d);
        } else {
            export_declarations();
        }
        export_notation();
    }
};

void export_as_lowtext(std::ostream & out, environment const & env,
        optional<list<name>> const & decls) {
    exporter(out, env)(decls);
}
}
