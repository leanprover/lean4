/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include <iostream>
#include <unordered_map>
#include "runtime/sstream.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/type_checker.h"
#include "kernel/quotient/quotient.h"
#include "checker/text_import.h"

namespace lean {

struct text_importer {
    std::unordered_map<unsigned, expr> m_expr;
    std::unordered_map<unsigned, name> m_name;
    std::unordered_map<unsigned, level> m_level;

    lowlevel_notations m_notations;

    environment m_env;

    text_importer(environment const & env) : m_env(env) {
        m_level[0] = {};
        m_name[0] = {};
    }

    levels read_levels(std::istream & in) {
        unsigned idx;
        buffer<level> ls;
        while (in >> idx) {
            ls.push_back(m_level.at(idx));
        }
        return to_list(ls);
    }

    level_param_names read_level_params(std::istream & in) {
        unsigned idx;
        buffer<name> ls;
        while (in >> idx) {
            ls.push_back(m_name.at(idx));
        }
        return to_list(ls);
    }

    void handle_ind(std::istream & in) {
        unsigned num_params, name_idx, type_idx, num_intros;
        in >> num_params >> name_idx >> type_idx >> num_intros;

        buffer<inductive::intro_rule> intros;
        for (unsigned i = 0; i < num_intros; i++) {
            unsigned name_idx, type_idx; in >> name_idx >> type_idx;
            intros.push_back(inductive::mk_intro_rule(m_name.at(name_idx), m_expr.at(type_idx)));
        }

        auto ls = read_level_params(in);

        inductive::inductive_decl decl(m_name.at(name_idx), ls, num_params, m_expr.at(type_idx), to_list(intros));
        m_env = inductive::add_inductive(m_env, decl, true).first;
    }

    void handle_def(std::istream & in) {
        unsigned name_idx, type_idx, val_idx;
        in >> name_idx >> type_idx >> val_idx;
        auto ls = read_level_params(in);

        auto decl =
            type_checker(m_env).is_prop(m_expr.at(type_idx)) ?
                mk_theorem(m_name.at(name_idx), ls, m_expr.at(type_idx), m_expr.at(val_idx)) :
                mk_definition(m_env, m_name.at(name_idx), ls, m_expr.at(type_idx), m_expr.at(val_idx), true, true);

        m_env = m_env.add(check(m_env, decl));
    }

    void handle_ax(std::istream & in) {
        unsigned name_idx, type_idx;
        in >> name_idx >> type_idx;
        auto ls = read_level_params(in);
        m_env = m_env.add(check(m_env, mk_axiom(m_name.at(name_idx), ls, m_expr.at(type_idx))));
    }

    void handle_notation(std::istream & in, lowlevel_notation_kind kind) {
        unsigned name_idx, prec;
        in >> name_idx >> prec;

        std::string token;
        std::getline(in, token);
        if (!token.empty() && token.front())
            token.erase(token.begin());
        if (!token.empty() && token.back() == '\n')
            token.erase(token.end() - 1);

        m_notations[m_name.at(name_idx)] = { kind, token, prec };
    }

    binder_info read_binder_info(std::string const & tok) {
        if (tok == "#BI") {
            return mk_implicit_binder_info();
        } else if (tok == "#BS") {
            return mk_strict_implicit_binder_info();
        } else if (tok == "#BC") {
            return mk_inst_implicit_binder_info();
        } else if (tok == "#BD") {
            return {};
        } else {
            throw exception(sstream() << "unknown binder info: " << tok);
        }
    }

    void handle_line(std::string const & line) {
        std::istringstream in(line);

        unsigned idx;
        std::string cmd;
        in >> cmd;
        if (cmd == "#IND") {
            handle_ind(in);
        } else if (cmd == "#DEF") {
            handle_def(in);
        } else if (cmd == "#AX") {
            handle_ax(in);
        } else if (cmd == "#QUOT") {
            m_env = declare_quotient(m_env);
        } else if (cmd == "#PREFIX") {
            handle_notation(in, lowlevel_notation_kind::Prefix);
        } else if (cmd == "#POSTFIX") {
            handle_notation(in, lowlevel_notation_kind::Postfix);
        } else if (cmd == "#INFIX") {
            handle_notation(in, lowlevel_notation_kind::Infix);
        } else if (std::istringstream(cmd) >> idx) {
            std::string kind;
            in >> kind;

            if (kind == "#NS") {
                unsigned p; std::string limb; in >> p >> std::skipws >> limb;
                m_name[idx] = name(m_name.at(p), limb.c_str());
            } else if (kind == "#NI") {
                unsigned p, limb; in >> p >> limb;
                m_name[idx] = name(m_name.at(p), limb);
            } else if (kind == "#US") {
                unsigned l1; in >> l1;
                m_level[idx] = mk_succ(m_level.at(l1));
            } else if (kind == "#UM") {
                unsigned l1, l2; in >> l1 >> l2;
                m_level[idx] = mk_max(m_level.at(l1), m_level.at(l2));
            } else if (kind == "#UIM") {
                unsigned l1, l2; in >> l1 >> l2;
                m_level[idx] = mk_imax(m_level.at(l1), m_level.at(l2));
            } else if (kind == "#UP") {
                unsigned i1; in >> i1;
                m_level[idx] = mk_param_univ(m_name.at(i1));
            } else if (kind == "#EV") {
                unsigned v; in >> v;
                m_expr[idx] = mk_var(v);
            } else if (kind == "#ES") {
                unsigned l; in >> l;
                m_expr[idx] = mk_sort(m_level.at(l));
            } else if (kind == "#EC") {
                unsigned n; in >> n;
                auto ls = read_levels(in);
                m_expr[idx] = mk_constant(m_name.at(n), ls);
            } else if (kind == "#EA") {
                unsigned e1, e2; in >> e1 >> e2;
                m_expr[idx] = mk_app(m_expr.at(e1), m_expr.at(e2));
            } else if (kind == "#EZ") {
                unsigned n, t, v, b; in >> n >> t >> v >> b;
                m_expr[idx] = mk_let(m_name.at(n), m_expr.at(t), m_expr.at(v), m_expr.at(b));
            } else if (kind == "#EL") {
                unsigned n, t, e; std::string b; in >> b >> n >> t >> e;
                m_expr[idx] = mk_lambda(m_name.at(n), m_expr.at(t), m_expr.at(e), read_binder_info(b));
            } else if (kind == "#EP") {
                unsigned n, t, e; std::string b; in >> b >> n >> t >> e;
                m_expr[idx] = mk_pi(m_name.at(n), m_expr.at(t), m_expr.at(e), read_binder_info(b));
            } else {
                throw exception(sstream() << "unknown term definition kind: " << kind);
            }
        } else {
            throw exception(sstream() << "unknown command: " << cmd);
        }
    }
};

void import_from_text(std::istream & in, environment & env, lowlevel_notations & notations) {
    text_importer importer(env);

    std::string line;
    unsigned line_num = 0;
    while (std::getline(in, line)) {
        line_num++;
        try {
            importer.handle_line(line);
        } catch (throwable & t) {
            throw exception(sstream() << "line " << line_num << ": " << t.what());
        } catch (std::exception & e) {
            throw exception(sstream() << "line " << line_num << ": " << e.what());
        }
    }

    env = importer.m_env;
    notations = std::move(importer.m_notations);
}

}
