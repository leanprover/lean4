/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include "kernel/expr_maps.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/max_sharing.h"
#include "library/module.h"
#include "library/unfold_macros.h"

namespace lean {
template<typename T>
using level_map = typename std::unordered_map<level, T, level_hash, level_eq>;

template<typename T>
using name_hmap = typename std::unordered_map<name, T, name_hash, name_eq>;


class exporter {
    std::ostream &        m_out;
    environment           m_env;
    bool                  m_all;
    name_set              m_exported;
    max_sharing_fn        m_max_sharing;
    name_hmap<unsigned>   m_name2idx;
    level_map<unsigned>   m_level2idx;
    expr_map<unsigned>    m_expr2idx;

    void mark(name const & n) {
        m_exported.insert(n);
    }

    bool already_exported(name const & n) {
        return m_exported.contains(n);
    }

    unsigned export_name(name const & n) {
        auto it = m_name2idx.find(n);
        if (it != m_name2idx.end())
            return it->second;
        unsigned i;
        if (n.is_anonymous()) {
            lean_unreachable();
        } else if (n.is_string()) {
            unsigned p = export_name(n.get_prefix());
            i = m_name2idx.size();
            m_out << i << " #NS " << p << " " << n.get_string() << "\n";
        } else {
            unsigned p = export_name(n.get_prefix());
            i = m_name2idx.size();
            m_out << i << " #NI " << p << " " << n.get_numeral() << "\n";
        }
        m_name2idx.insert(mk_pair(n, i));
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
            i  = m_level2idx.size();
            m_out << i << " #US " << l1 << "\n";
            break;
        case level_kind::Max:
            l1 = export_level(max_lhs(l));
            l2 = export_level(max_rhs(l));
            i  = m_level2idx.size();
            m_out << i << " #UM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::IMax:
            l1 = export_level(imax_lhs(l));
            l2 = export_level(imax_rhs(l));
            i  = m_level2idx.size();
            m_out << i << " #UIM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::Param:
            n = export_name(param_id(l));
            i = m_level2idx.size();
            m_out << i << " #UP " << n << "\n";
            break;
        case level_kind::Global:
            n = export_name(global_id(l));
            i = m_level2idx.size();
            m_out << i << " #UG " << n << "\n";
            break;
        case level_kind::Meta:
            throw exception("invald 'export', universe meta-variables cannot be exported");
        }
        m_level2idx.insert(mk_pair(l, i));
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
        unsigned i  = m_expr2idx.size();
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
        unsigned i  = m_expr2idx.size();
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
            i = m_expr2idx.size();
            m_out << i << " #EV " << var_idx(e) << "\n";
            break;
        case expr_kind::Sort:
            l = export_level(sort_level(e));
            i = m_expr2idx.size();
            m_out << i << " #ES " << l << "\n";
            break;
        case expr_kind::Constant:
            i = export_const(e);
            break;
        case expr_kind::App:
            e1 = export_expr(app_fn(e));
            e2 = export_expr(app_arg(e));
            i  = m_expr2idx.size();
            m_out << i << " #EA " << e1 << " " << e2 << "\n";
            break;
        case expr_kind::Lambda:
            i  = export_binding(e, "#EL");
            break;
        case expr_kind::Pi:
            i  = export_binding(e, "#EP");
            break;
        case expr_kind::Meta:
            throw exception("invald 'export', meta-variables cannot be exported");
        case expr_kind::Local:
            throw exception("invald 'export', local constants cannot be exported");
        case expr_kind::Macro:
            throw exception("invald 'export', macros cannot be exported");
        }
        m_expr2idx.insert(mk_pair(e, i));
        return i;
    }

    unsigned export_root_expr(expr const & e) {
        return export_expr(m_max_sharing(unfold_all_macros(m_env, e)));
    }

    void export_dependencies(expr const & e) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_constant(e)) {
                    name const & n = const_name(e);
                    export_declaration(n);
                }
                return true;
            });
    }

    void export_definition(declaration const & d) {
        if (already_exported(d.get_name()))
            return;
        mark(d.get_name());
        unsigned n = export_name(d.get_name());
        buffer<unsigned> ps;
        if (m_all) {
            export_dependencies(d.get_type());
            export_dependencies(d.get_value());
        }
        for (name const & p : d.get_univ_params())
            ps.push_back(export_name(p));
        unsigned t = export_root_expr(d.get_type());
        unsigned v = export_root_expr(d.get_value());
        m_out << "#DEF " << n;
        for (unsigned p : ps)
            m_out << " " << p;
        m_out << " | " << t << " " << v << "\n";
    }

    void export_axiom(declaration const & d) {
        if (inductive::is_intro_rule(m_env, d.get_name()) || inductive::is_elim_rule(m_env, d.get_name()))
            return;
        if (already_exported(d.get_name()))
            return;
        mark(d.get_name());
        unsigned n = export_name(d.get_name());
        buffer<unsigned> ps;
        if (m_all)
            export_dependencies(d.get_type());
        for (name const & p : d.get_univ_params())
            ps.push_back(export_name(p));
        unsigned t = export_root_expr(d.get_type());
        m_out << "#AX " << n;
        for (unsigned p : ps)
            m_out << " " << p;
        m_out << " | " << t << "\n";
    }

    void export_inductive(name const & n) {
        if (already_exported(n))
            return;
        mark(n);
        std::tuple<level_param_names, unsigned, list<inductive::inductive_decl>> decls =
            *inductive::is_inductive_decl(m_env, n);
        if (m_all) {
            for (inductive::inductive_decl const & d : std::get<2>(decls)) {
                export_dependencies(inductive::inductive_decl_type(d));
                for (inductive::intro_rule const & c : inductive::inductive_decl_intros(d)) {
                    export_dependencies(inductive::intro_rule_type(c));
                }
            }
        }
        for (name const & p : std::get<0>(decls))
            export_name(p);
        for (inductive::inductive_decl const & d : std::get<2>(decls)) {
            export_name(inductive::inductive_decl_name(d));
            export_root_expr(inductive::inductive_decl_type(d));
            for (inductive::intro_rule const & c : inductive::inductive_decl_intros(d)) {
                export_name(inductive::intro_rule_name(c));
                export_root_expr(inductive::intro_rule_type(c));
            }
        }
        m_out << "#BIND " << std::get<1>(decls) << " " << length(std::get<2>(decls));
        for (name const & p : std::get<0>(decls))
            m_out << " " << export_name(p);
        m_out << "\n";
        for (inductive::inductive_decl const & d : std::get<2>(decls)) {
            m_out << "#IND " << export_name(inductive::inductive_decl_name(d)) << " "
                  << export_root_expr(inductive::inductive_decl_type(d)) << "\n";
            for (inductive::intro_rule const & c : inductive::inductive_decl_intros(d)) {
                m_out << "#INTRO " << export_name(inductive::intro_rule_name(c)) << " "
                      << export_root_expr(inductive::intro_rule_type(c)) << "\n";
            }
        }
        m_out << "#EIND\n";
    }

    void export_declaration(name const & n) {
        if (inductive::is_inductive_decl(m_env, n)) {
            export_inductive(n);
        } else {
            declaration const & d = m_env.get(n);
            if (d.is_definition())
                export_definition(d);
            else
                export_axiom(d);
        }
    }

    void export_declarations() {
        if (m_all) {
            m_env.for_each_declaration([&](declaration const & d) {
                    export_declaration(d.get_name());
                });
        } else {
            buffer<name> ns;
            to_buffer(get_curr_module_decl_names(m_env), ns);
            std::reverse(ns.begin(), ns.end());
            for (name const & n : ns) {
                export_declaration(n);
            }
        }
    }

    void export_direct_imports() {
        if (!m_all) {
            buffer<module_name> imports;
            to_buffer(get_curr_module_imports(m_env), imports);
            std::reverse(imports.begin(), imports.end());
            for (module_name const & m : imports) {
                unsigned n = export_name(m.get_name());
                if (m.is_relative()) {
                    m_out << "#RI " << *m.get_k() << " " << n << "\n";
                } else {
                    m_out << "#DI " << n << "\n";
                }
            }
        }
    }

    void export_global_universes() {
        if (m_all) {
            m_env.for_each_universe([&](name const & u) {
                    unsigned n = export_name(u);
                    m_out << "#UNI " << n << "\n";
                });
        } else {
            buffer<name> ns;
            to_buffer(get_curr_module_univ_names(m_env), ns);
            std::reverse(ns.begin(), ns.end());
            for (name const & u : ns) {
                unsigned n = export_name(u);
                m_out << "#UNI " << n << "\n";
            }
        }
    }

public:
    exporter(std::ostream & out, environment const & env, bool all):m_out(out), m_env(env), m_all(all) {}

    void operator()() {
        m_name2idx.insert(mk_pair(name(), 0));
        m_level2idx.insert(mk_pair(level(), 0));
        export_direct_imports();
        export_global_universes();
        export_declarations();
    }
};

void export_module_as_lowtext(std::ostream & out, environment const & env) {
    exporter(out, env, false)();
}

void export_all_as_lowtext(std::ostream & out, environment const & env) {
    exporter(out, env, true)();
}
}
