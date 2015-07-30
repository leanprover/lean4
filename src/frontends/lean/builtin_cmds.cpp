/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "kernel/quotient/quotient.h"
#include "kernel/hits/hits.h"
#include "kernel/default_converter.h"
#include "library/io_state_stream.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/locals.h"
#include "library/coercion.h"
#include "library/reducible.h"
#include "library/normalize.h"
#include "library/print.h"
#include "library/noncomputable.h"
#include "library/class.h"
#include "library/flycheck.h"
#include "library/abbreviation.h"
#include "library/util.h"
#include "library/user_recursors.h"
#include "library/pp_options.h"
#include "library/composition_manager.h"
#include "library/definitional/projection.h"
#include "library/simplifier/simp_rule_set.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/inductive_cmd.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/migrate_cmd.h"
#include "frontends/lean/find_cmd.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parse_table.h"

namespace lean {
static void print_coercions(parser & p, optional<name> const & C) {
    environment const & env = p.env();
    options opts = p.regular_stream().get_options();
    opts = opts.update(get_pp_coercions_option_name(), true);
    io_state_stream out = p.regular_stream().update_options(opts);
    char const * arrow = get_pp_unicode(opts) ? "↣" : ">->";
    for_each_coercion_user(env, [&](name const & C1, name const & c, name const & D) {
            if (!C || *C == C1)
                out << C1 << " " << arrow << " " << D << " : " << c << endl;
        });
    for_each_coercion_sort(env, [&](name const & C1, name const & c) {
            if (!C || *C == C1)
                out << C1 << " " << arrow << " [sort-class] : " << c << endl;
        });
    for_each_coercion_fun(env, [&](name const & C1, name const & c) {
            if (!C || *C == C1)
                out << C1 << " " << arrow << " [fun-class] : " << c << endl;
        });
}

struct print_axioms_deps {
    environment     m_env;
    io_state_stream m_ios;
    name_set        m_visited;
    bool            m_use_axioms;
    print_axioms_deps(environment const & env, io_state_stream const & ios):
        m_env(env), m_ios(ios), m_use_axioms(false) {}

    void visit(name const & n) {
        if (m_visited.contains(n))
            return;
        m_visited.insert(n);
        declaration const & d = m_env.get(n);
        if (!d.is_definition() && !m_env.is_builtin(n)) {
            m_use_axioms = true;
            m_ios << d.get_name() << "\n";
        }
        visit(d.get_type());
        if (d.is_definition())
            visit(d.get_value());
    }

    void visit(expr const & e) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_constant(e))
                    visit(const_name(e));
                return true;
            });
    }

    void operator()(name const & n) {
        visit(n);
        if (!m_use_axioms)
            m_ios << "no axioms" << endl;
    }
};

static void print_axioms(parser & p) {
    if (p.curr_is_identifier()) {
        name c = p.check_constant_next("invalid 'print axioms', constant expected");
        print_axioms_deps(p.env(), p.regular_stream())(c);
    } else {
        bool has_axioms = false;
        environment const & env = p.env();
        env.for_each_declaration([&](declaration const & d) {
                name const & n = d.get_name();
                if (!d.is_definition() && !env.is_builtin(n)) {
                    p.regular_stream() << n << " : " << d.get_type() << endl;
                    has_axioms = true;
                }
            });
        if (!has_axioms)
            p.regular_stream() << "no axioms" << endl;
    }
}

static void print_prefix(parser & p) {
    name prefix = p.check_id_next("invalid 'print prefix' command, identifier expected");
    environment const & env = p.env();
    buffer<declaration> to_print;
    env.for_each_declaration([&](declaration const & d) {
            if (is_prefix_of(prefix, d.get_name())) {
                to_print.push_back(d);
            }
        });
    std::sort(to_print.begin(), to_print.end(), [](declaration const & d1, declaration const & d2) { return d1.get_name() < d2.get_name(); });
    for (declaration const & d : to_print) {
        p.regular_stream() << d.get_name() << " : " << d.get_type() << endl;
    }
    if (to_print.empty())
        p.regular_stream() << "no declaration starting with prefix '" << prefix << "'" << endl;
}

static void print_fields(parser const & p, name const & S, pos_info const & pos) {
    environment const & env = p.env();
    if (!is_structure(env, S))
        throw parser_error(sstream() << "invalid 'print fields' command, '" << S << "' is not a structure", pos);
    buffer<name> field_names;
    get_structure_fields(env, S, field_names);
    for (name const & field_name : field_names) {
        declaration d = env.get(field_name);
        p.regular_stream() << d.get_name() << " : " << d.get_type() << endl;
    }
}

static bool uses_token(unsigned num, notation::transition const * ts, name const & token) {
    for (unsigned i = 0; i < num; i++) {
        if (ts[i].get_token() == token)
            return true;
    }
    return false;
}

static bool uses_some_token(unsigned num, notation::transition const * ts, buffer<name> const & tokens) {
    return
        tokens.empty() ||
        std::any_of(tokens.begin(), tokens.end(), [&](name const & token) { return uses_token(num, ts, token); });
}

static bool print_parse_table(parser const & p, parse_table const & t, bool nud, buffer<name> const & tokens, bool tactic_table = false) {
    bool found = false;
    io_state ios = p.ios();
    options os   = ios.get_options();
    os = os.update_if_undef(get_pp_full_names_option_name(), true);
    os = os.update(get_pp_notation_option_name(), false);
    os = os.update(get_pp_preterm_name(), true);
    ios.set_options(os);
    optional<token_table> tt(get_token_table(p.env()));
    t.for_each([&](unsigned num, notation::transition const * ts, list<pair<unsigned, expr>> const & overloads) {
            if (uses_some_token(num, ts, tokens)) {
                io_state_stream out = regular(p.env(), ios);
                if (tactic_table)
                    out << "tactic notation ";
                found = true;
                notation::display(out, num, ts, overloads, nud, tt);
            }
        });
    return found;
}

static void print_notation(parser & p) {
    buffer<name> tokens;
    while (p.curr_is_keyword()) {
        tokens.push_back(p.get_token_info().token());
        p.next();
    }
    bool found = false;
    if (print_parse_table(p, get_nud_table(p.env()), true, tokens))
        found = true;
    if (print_parse_table(p, get_led_table(p.env()), false, tokens))
        found = true;
    if (!found)
        p.regular_stream() << "no notation" << endl;
}

static void print_metaclasses(parser const & p) {
    buffer<name> c;
    get_metaclasses(c);
    for (name const & n : c)
        p.regular_stream() << "[" << n << "]" << endl;
}

static void print_definition(parser const & p, name const & n, pos_info const & pos) {
    environment const & env = p.env();
    declaration d = env.get(n);
    io_state_stream out = p.regular_stream();
    options opts        = out.get_options();
    opts                = opts.update_if_undef(get_pp_beta_name(), false);
    io_state_stream new_out = out.update_options(opts);
    if (d.is_axiom())
        throw parser_error(sstream() << "invalid 'print definition', theorem '" << n
                           << "' is not available (suggestion: use command 'reveal " << n << "')", pos);
    if (!d.is_definition())
        throw parser_error(sstream() << "invalid 'print definition', '" << n << "' is not a definition", pos);
    new_out << d.get_value() << endl;
}

static void print_attributes(parser const & p, name const & n) {
    environment const & env = p.env();
    io_state_stream out = p.regular_stream();
    if (is_coercion(env, n))
        out << " [coercion]";
    if (is_class(env, n))
        out << " [class]";
    if (is_instance(env, n))
        out << " [instance]";
    if (is_simp_rule(env, n))
        out << " [simp]";
    if (is_congr_rule(env, n))
        out << " [congr]";
    switch (get_reducible_status(env, n)) {
    case reducible_status::Reducible:      out << " [reducible]"; break;
    case reducible_status::Irreducible:    out << " [irreducible]"; break;
    case reducible_status::Quasireducible: out << " [quasireducible]"; break;
    case reducible_status::Semireducible:  break;
    }
}

static void print_inductive(parser const & p, name const & n, pos_info const & pos) {
    environment const & env = p.env();
    io_state_stream out = p.regular_stream();
    if (auto idecls = inductive::is_inductive_decl(env, n)) {
        level_param_names ls; unsigned nparams; list<inductive::inductive_decl> dlist;
        std::tie(ls, nparams, dlist) = *idecls;
        if (is_structure(env, n))
            out << "structure";
        else
            out << "inductive";
        out << " " << n;
        print_attributes(p, n);
        out << " : " << env.get(n).get_type() << "\n";
        if (is_structure(env, n)) {
            out << "fields:\n";
            print_fields(p, n, pos);
        } else {
            out << "constructors:\n";
            buffer<name> constructors;
            get_intro_rule_names(env, n, constructors);
            for (name const & c : constructors) {
                out << c << " : " << env.get(c).get_type() << "\n";
            }
        }
    } else {
        throw parser_error(sstream() << "invalid 'print inductive', '" << n << "' is not an inductive declaration", pos);
    }
}

static void print_recursor_info(parser & p) {
    name c = p.check_constant_next("invalid 'print [recursor]', constant expected");
    auto out = p.regular_stream();
    recursor_info info = get_recursor_info(p.env(), c);
    out << "recursor information\n"
        << "  num. parameters:          " << info.get_num_params() << "\n"
        << "  num. indices:             " << info.get_num_indices() << "\n"
        << "  universe param pos.:     ";
    for (unsigned idx : info.get_universe_pos()) {
        if (idx == recursor_info::get_motive_univ_idx()) {
            out << " [motive univ]";
        } else {
            out << " " << idx;
        }
    }
    out << "\n";
    out << "  motive pos.:              " << info.get_motive_pos() + 1 << "\n"
        << "  major premise pos.:       " << info.get_major_pos() + 1 << "\n"
        << "  dep. elimination:         " << info.has_dep_elim() << "\n";
    if (info.get_num_params() > 0) {
        out << "  parameters pos. at major:";
        for (optional<unsigned> const & p : info.get_params_pos()) {
            if (p)
                out << " " << *p+1;
            else
                out << " [instance]";
        }
        out << "\n";
    }
    if (info.get_num_indices() > 0) {
        out << "  indices pos. at major:   ";
        for (unsigned p : info.get_indices_pos())
            out << " " << p+1;
        out << "\n";
    }
}

static bool print_constant(parser const & p, char const * kind, declaration const & d, bool is_def = false) {
    io_state_stream out = p.regular_stream();
    if (d.is_definition() && is_marked_noncomputable(p.env(), d.get_name()))
        out << "noncomputable ";
    if (is_protected(p.env(), d.get_name()))
        out << "protected ";
    out << kind << " " << d.get_name();
    print_attributes(p, d.get_name());
    out << " : " << d.get_type();
    if (is_def)
        out << " :=";
    out << "\n";
    return true;
}

bool print_id_info(parser const & p, name const & id, bool show_value, pos_info const & pos) {
    // declarations
    try {
        environment const & env = p.env();
        io_state_stream out = p.regular_stream();
        try {
            list<name> cs = p.to_constants(id, "", pos);
            bool first = true;
            for (name const & c : cs) {
                if (first) first = false; else out << "\n";
                declaration const & d = env.get(c);
                if (d.is_theorem()) {
                    print_constant(p, "theorem", d, show_value);
                    if (show_value)
                        print_definition(p, c, pos);
                } else if (d.is_axiom() || d.is_constant_assumption()) {
                    if (inductive::is_inductive_decl(env, c)) {
                        print_inductive(p, c, pos);
                    } else if (inductive::is_intro_rule(env, c)) {
                        print_constant(p, "constructor", d);
                    } else if (inductive::is_elim_rule(env, c)) {
                        print_constant(p, "eliminator", d);
                    } else if (is_quotient_decl(env, c)) {
                        print_constant(p, "builtin-quotient-type-constant", d);
                    } else if (is_hits_decl(env, c)) {
                        print_constant(p, "builtin-HIT-constant", d);
                    } else if (d.is_axiom()) {
                        if (p.in_theorem_queue(d.get_name())) {
                            print_constant(p, "theorem", d);
                            if (show_value) {
                                out << "'" << d.get_name() << "' is still in the theorem queue, use command 'reveal "
                                    << d.get_name() << "' to access its definition.\n";
                            }
                        } else {
                            print_constant(p, "axiom", d);
                        }
                    } else {
                        print_constant(p, "constant", d);
                    }
                } else if (d.is_definition()) {
                    print_constant(p, "definition", d, show_value);
                    if (show_value)
                        print_definition(p, c, pos);
                }
            }
            return true;
        } catch (exception & ex) {}

        // variables and parameters
        if (expr const * type = p.get_local(id)) {
            if (is_local(*type)) {
                if (p.is_local_variable(*type)) {
                    out << "variable " << id << " : " << mlocal_type(*type) << "\n";
                } else {
                    out << "parameter " << id << " : " << mlocal_type(*type) << "\n";
                }
                return true;
            }
        }

        // options
        for (auto odecl : get_option_declarations()) {
            auto opt = odecl.second;
            if (opt.get_name() == id || opt.get_name() == name("lean") + id) {
                out << "option  " << opt.get_name() << " (" << opt.kind() << ") "
                    << opt.get_description() << " (default: " << opt.get_default_value() << ")" << endl;
                return true;
            }
        }
    } catch (exception &) {}
    return false;
}

bool print_token_info(parser const & p, name const & tk) {
    buffer<name> tokens;
    tokens.push_back(tk);
    bool found = false;
    if (print_parse_table(p, get_nud_table(p.env()), true, tokens)) {
        found = true;
    }
    if (print_parse_table(p, get_led_table(p.env()), false, tokens)) {
        found = true;
    }
    bool tactic_table = true;
    if (print_parse_table(p, get_tactic_nud_table(p.env()), true, tokens, tactic_table)) {
        found = true;
    }
    if (print_parse_table(p, get_tactic_led_table(p.env()), false, tokens, tactic_table)) {
        found = true;
    }
    return found;
}

bool print_polymorphic(parser & p) {
    auto pos = p.pos();
    try {
        name id = p.check_id_next("");
        bool show_value = true;
        if (print_id_info(p, id, show_value, pos))
            return true;
    } catch (exception &) {}

    // notation
    if (p.curr_is_keyword()) {
        name tk = p.get_token_info().token();
        if (print_token_info(p, tk)) {
            p.next();
            return true;
        }
    }
    return false;
}

static void print_reducible_info(parser & p, reducible_status s1) {
    buffer<name> r;
    for_each_reducible(p.env(), [&](name const & n, reducible_status s2) {
            if (s1 == s2)
                r.push_back(n);
        });
    io_state_stream out = p.regular_stream();
    std::sort(r.begin(), r.end());
    for (name const & n : r)
        out << n << "\n";
}

static void print_simp_rules(parser & p) {
    io_state_stream out = p.regular_stream();
    simp_rule_sets s;
    name ns;
    if (p.curr_is_identifier()) {
        ns = p.get_name_val();
        p.next();
        s = get_simp_rule_sets(p.env(), ns);
    } else {
        s = get_simp_rule_sets(p.env());
    }
    format header;
    if (!ns.is_anonymous())
        header = format(" at namespace '") + format(ns) + format("'");
    out << s.pp_simp(out.get_formatter(), header);
}

static void print_congr_rules(parser & p) {
    io_state_stream out = p.regular_stream();
    simp_rule_sets s = get_simp_rule_sets(p.env());
    out << s.pp_congr(out.get_formatter());
}

environment print_cmd(parser & p) {
    flycheck_information info(p.regular_stream());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.regular_stream() << "print result:\n";
    }
    if (p.curr() == scanner::token_kind::String) {
        p.regular_stream() << p.get_str_val() << endl;
        p.next();
    } else if (p.curr_is_token_or_id(get_raw_tk())) {
        p.next();
        expr e = p.parse_expr();
        io_state_stream out = p.regular_stream();
        options opts = out.get_options();
        opts = opts.update(get_pp_notation_option_name(), false);
        out.update_options(opts) << e << endl;
    } else if (p.curr_is_token_or_id(get_reducible_tk())) {
        p.next();
        print_reducible_info(p, reducible_status::Reducible);
    } else if (p.curr_is_token_or_id(get_quasireducible_tk())) {
        p.next();
        print_reducible_info(p, reducible_status::Quasireducible);
    } else if (p.curr_is_token_or_id(get_irreducible_tk())) {
        p.next();
        print_reducible_info(p, reducible_status::Irreducible);
    } else if (p.curr_is_token_or_id(get_options_tk())) {
        p.next();
        p.regular_stream() << p.ios().get_options() << endl;
    } else if (p.curr_is_token_or_id(get_trust_tk())) {
        p.next();
        p.regular_stream() << "trust level: " << p.env().trust_lvl() << endl;
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
        auto pos = p.pos();
        name id  = p.check_id_next("invalid 'print definition', constant expected");
        list<name> cs = p.to_constants(id, "invalid 'print definition', constant expected", pos);
        bool first = true;
        for (name const & c : cs) {
            if (first)
                first = false;
            else
                p.regular_stream() << "\n";
            declaration const & d = p.env().get(c);
            if (d.is_theorem()) {
                print_constant(p, "theorem", d);
                print_definition(p, c, pos);
            } else if (d.is_definition()) {
                print_constant(p, "definition", d);
                print_definition(p, c, pos);
            } else {
                throw parser_error(sstream() << "invalid 'print definition', '" << c << "' is not a definition", pos);
            }
        }
    } else if (p.curr_is_token_or_id(get_instances_tk())) {
        p.next();
        name c = p.check_constant_next("invalid 'print instances', constant expected");
        environment const & env = p.env();
        for (name const & i : get_class_instances(env, c)) {
            p.regular_stream() << i << " : " << env.get(i).get_type() << endl;
        }
        if (list<name> derived_insts = get_class_derived_trans_instances(env, c)) {
            p.regular_stream() << "Derived transitive instances:\n";
            for (name const & i : derived_insts) {
                p.regular_stream() << i << " : " << env.get(i).get_type() << endl;
            }
        }
    } else if (p.curr_is_token_or_id(get_classes_tk())) {
        p.next();
        environment const & env = p.env();
        buffer<name> classes;
        get_classes(env, classes);
        std::sort(classes.begin(), classes.end());
        for (name const & c : classes) {
            p.regular_stream() << c << " : " << env.get(c).get_type() << endl;
        }
    } else if (p.curr_is_token_or_id(get_prefix_tk())) {
        p.next();
        print_prefix(p);
    } else if (p.curr_is_token_or_id(get_coercions_tk())) {
        p.next();
        optional<name> C;
        if (p.curr_is_identifier())
            C = p.check_constant_next("invalid 'print coercions', constant expected");
        print_coercions(p, C);
    } else if (p.curr_is_token_or_id(get_metaclasses_tk())) {
        p.next();
        print_metaclasses(p);
    } else if (p.curr_is_token_or_id(get_axioms_tk())) {
        p.next();
        print_axioms(p);
    } else if (p.curr_is_token_or_id(get_fields_tk())) {
        p.next();
        auto pos = p.pos();
        name S = p.check_constant_next("invalid 'print fields' command, constant expected");
        print_fields(p, S, pos);
    } else if (p.curr_is_token_or_id(get_notation_tk())) {
        p.next();
        print_notation(p);
    } else if (p.curr_is_token_or_id(get_inductive_tk())) {
        p.next();
        auto pos = p.pos();
        name c = p.check_constant_next("invalid 'print inductive', constant expected");
        print_inductive(p, c, pos);
    } else if (p.curr_is_token(get_recursor_tk())) {
        p.next();
        p.check_token_next(get_rbracket_tk(), "invalid 'print [recursor]', ']' expected");
        print_recursor_info(p);
    } else if (p.curr_is_token(get_simp_attr_tk())) {
        p.next();
        print_simp_rules(p);
    } else if (p.curr_is_token(get_congr_attr_tk())) {
        p.next();
        print_congr_rules(p);
    } else if (print_polymorphic(p)) {
    } else {
        throw parser_error("invalid print command", p.pos());
    }
    return p.env();
}

environment section_cmd(parser & p) {
    name n;
    if (p.curr_is_identifier())
        n = p.check_atomic_id_next("invalid section, atomic identifier expected");
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Section, n);
}

environment namespace_cmd(parser & p) {
    auto pos = p.pos();
    name n = p.check_atomic_id_next("invalid namespace declaration, atomic identifier expected");
    if (is_root_namespace(n))
        throw parser_error(sstream() << "invalid namespace name, '" << n << "' is reserved", pos);
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Namespace, n);
}

static environment redeclare_aliases(environment env, parser & p,
                                     list<pair<name, level>> old_level_entries,
                                     list<pair<name, expr>> old_entries) {
    environment const & old_env = p.env();
    if (!in_section(old_env))
        return env;
    list<pair<name, expr>> new_entries = p.get_local_entries();
    buffer<pair<name, expr>> to_redeclare;
    unsigned new_len = length(new_entries);
    unsigned old_len = length(old_entries);
    lean_assert(old_len >= new_len);
    name_set popped_locals;
    while (old_len > new_len) {
        pair<name, expr> entry = head(old_entries);
        if (is_local_ref(entry.second))
            to_redeclare.push_back(entry);
        else if (is_local(entry.second))
            popped_locals.insert(mlocal_name(entry.second));
        old_entries = tail(old_entries);
        old_len--;
    }
    name_set popped_levels;
    list<pair<name, level>> new_level_entries = p.get_local_level_entries();
    while (!is_eqp(old_level_entries, new_level_entries)) {
        level const & l = head(old_level_entries).second;
        if (is_param(l))
            popped_levels.insert(param_id(l));
        old_level_entries = tail(old_level_entries);
    }

    for (auto const & entry : to_redeclare) {
        expr new_ref = update_local_ref(entry.second, popped_levels, popped_locals);
        if (!is_constant(new_ref))
            env = p.add_local_ref(env, entry.first, new_ref);
    }
    return env;
}

environment end_scoped_cmd(parser & p) {
    list<pair<name, level>> level_entries = p.get_local_level_entries();
    list<pair<name, expr>> entries        = p.get_local_entries();
    p.pop_local_scope();
    if (p.curr_is_identifier()) {
        name n = p.check_atomic_id_next("invalid end of scope, atomic identifier expected");
        environment env = pop_scope(p.env(), p.ios(), n);
        return redeclare_aliases(env, p, level_entries, entries);
    } else {
        environment env = pop_scope(p.env(), p.ios());
        return redeclare_aliases(env, p, level_entries, entries);
    }
}

environment check_cmd(parser & p) {
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    e = expand_abbreviations(p.env(), e);
    auto tc = mk_type_checker(p.env(), p.mk_ngen());
    expr type = tc->check(e, ls).first;
    auto reg              = p.regular_stream();
    formatter fmt         = reg.get_formatter();
    options opts          = p.ios().get_options();
    opts                  = opts.update_if_undef(get_pp_metavar_args_name(), true);
    fmt                   = fmt.update_options(opts);
    unsigned indent       = get_pp_indent(opts);
    format r = group(fmt(e) + space() + colon() + nest(indent, line() + fmt(type)));
    flycheck_information info(p.regular_stream());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.regular_stream() << "check result:\n";
    }
    reg << mk_pair(r, opts) << endl;
    return p.env();
}

environment eval_cmd(parser & p) {
    bool whnf   = false;
    if (p.curr_is_token(get_whnf_tk())) {
        p.next();
        whnf = true;
    }
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    expr r;
    if (whnf) {
        auto tc = mk_type_checker(p.env(), p.mk_ngen());
        r = tc->whnf(e).first;
    } else {
        type_checker tc(p.env());
        bool eta = false;
        bool eval_nested_prop = false;
        r = normalize(tc, ls, e, eta, eval_nested_prop);
    }
    flycheck_information info(p.regular_stream());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.regular_stream() << "eval result:\n";
    }
    p.regular_stream() << r << endl;
    return p.env();
}

environment exit_cmd(parser & p) {
    flycheck_warning wrn(p.regular_stream());
    p.display_warning_pos(p.cmd_pos());
    p.regular_stream() << " using 'exit' to interrupt Lean" << endl;
    throw interrupt_parser();
}

environment set_option_cmd(parser & p) {
    auto id_kind = parse_option_name(p, "invalid set option, identifier (i.e., option name) expected");
    name id       = id_kind.first;
    option_kind k = id_kind.second;
    if (k == BoolOption) {
        if (p.curr_is_token_or_id(get_true_tk()))
            p.set_option(id, true);
        else if (p.curr_is_token_or_id(get_false_tk()))
            p.set_option(id, false);
        else
            throw parser_error("invalid Boolean option value, 'true' or 'false' expected", p.pos());
        p.next();
    } else if (k == StringOption) {
        if (!p.curr_is_string())
            throw parser_error("invalid option value, given option is not a string", p.pos());
        p.set_option(id, p.get_str_val());
        p.next();
    } else if (k == DoubleOption) {
        p.set_option(id, p.parse_double());
    } else if (k == UnsignedOption || k == IntOption) {
        p.set_option(id, p.parse_small_nat());
    } else {
        throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", p.pos());
    }
    p.updt_options();
    environment env = p.env();
    return update_fingerprint(env, p.get_options().hash());
}

static bool is_next_metaclass_tk(parser const & p) {
    return p.curr_is_token(get_lbracket_tk()) || p.curr_is_token(get_unfold_hints_bracket_tk());
}

static name parse_metaclass(parser & p) {
    if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        auto pos = p.pos();
        name n;
        while (!p.curr_is_token(get_rbracket_tk())) {
            if (p.curr_is_identifier())
                n = n.append_after(p.get_name_val().to_string().c_str());
            else if (p.curr_is_keyword() || p.curr_is_command())
                n = n.append_after(p.get_token_info().value().to_string().c_str());
            else if (p.curr_is_token(get_sub_tk()))
                n = n.append_after("-");
            else
                throw parser_error("invalid 'open' command, identifier or symbol expected", pos);
            p.next();
        }
        p.check_token_next(get_rbracket_tk(), "invalid 'open' command, ']' expected");
        if (!is_metaclass(n) && n != get_decls_tk() && n != get_declarations_tk())
            throw parser_error(sstream() << "invalid metaclass name '[" << n << "]'", pos);
        return n;
    } else if (p.curr_is_token(get_unfold_hints_bracket_tk())) {
        p.next();
        return get_unfold_hints_tk();
    } else {
        return name();
    }
}

static void parse_metaclasses(parser & p, buffer<name> & r) {
    if (p.curr_is_token(get_sub_tk())) {
        p.next();
        buffer<name> tmp;
        get_metaclasses(tmp);
        tmp.push_back(get_decls_tk());
        while (is_next_metaclass_tk(p)) {
            name m = parse_metaclass(p);
            tmp.erase_elem(m);
            if (m == get_declarations_tk())
                tmp.erase_elem(get_decls_tk());
        }
        r.append(tmp);
    } else {
        while (is_next_metaclass_tk(p)) {
            r.push_back(parse_metaclass(p));
        }
    }
}

static void check_identifier(parser & p, environment const & env, name const & ns, name const & id) {
    name full_id = ns + id;
    if (!env.find(full_id))
        throw parser_error(sstream() << "invalid 'open' command, unknown declaration '" << full_id << "'", p.pos());
}

// add id as an abbreviation for d
static environment add_abbrev(parser & p, environment const & env, name const & id, name const & d) {
    declaration decl = env.get(d);
    buffer<level> ls;
    for (name const & l : decl.get_univ_params())
        ls.push_back(mk_param_univ(l));
    expr value  = mk_constant(d, to_list(ls.begin(), ls.end()));
    name const & ns = get_namespace(env);
    name full_id    = ns + id;
    p.add_abbrev_index(full_id, d);
    environment new_env =
        module::add(env, check(env, mk_definition(env, full_id, decl.get_univ_params(), decl.get_type(), value)));
    if (full_id != id)
        new_env = add_expr_alias_rec(new_env, id, full_id);
    return new_env;
}

// open/export [class] id (as id)? (id ...) (renaming id->id id->id) (hiding id ... id)
environment open_export_cmd(parser & p, bool open) {
    environment env = p.env();
    unsigned fingerprint = 0;
    while (true) {
        buffer<name> metacls;
        parse_metaclasses(p, metacls);
        bool decls = false;
        if (metacls.empty() ||
            std::find(metacls.begin(), metacls.end(), get_decls_tk()) != metacls.end() ||
            std::find(metacls.begin(), metacls.end(), get_declarations_tk()) != metacls.end())
            decls = true;
        for (name const & n : metacls)
            fingerprint = hash(fingerprint, n.hash());
        auto pos   = p.pos();
        name ns    = p.check_id_next("invalid 'open/export' command, identifier expected");
        optional<name> real_ns = to_valid_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        fingerprint = hash(fingerprint, ns.hash());
        name as;
        if (p.curr_is_token_or_id(get_as_tk())) {
            p.next();
            as = p.check_id_next("invalid 'open/export' command, identifier expected");
        }
        if (open)
            env = using_namespace(env, p.ios(), ns, metacls);
        else
            env = export_namespace(env, p.ios(), ns, metacls);
        if (decls) {
            // Remark: we currently to not allow renaming and hiding of universe levels
            buffer<name> exceptions;
            bool found_explicit = false;
            while (p.curr_is_token(get_lparen_tk())) {
                p.next();
                if (p.curr_is_token_or_id(get_renaming_tk())) {
                    p.next();
                    while (p.curr_is_identifier()) {
                        name from_id = p.get_name_val();
                        p.next();
                        p.check_token_next(get_arrow_tk(), "invalid 'open/export' command renaming, '->' expected");
                        name to_id = p.check_id_next("invalid 'open/export' command renaming, identifier expected");
                        fingerprint = hash(hash(fingerprint, from_id.hash()), to_id.hash());
                        check_identifier(p, env, ns, from_id);
                        exceptions.push_back(from_id);
                        if (open)
                            env = add_expr_alias(env, as+to_id, ns+from_id);
                        else
                            env = add_abbrev(p, env, as+to_id, ns+from_id);
                    }
                } else if (p.curr_is_token_or_id(get_hiding_tk())) {
                    p.next();
                    while (p.curr_is_identifier()) {
                        name id = p.get_name_val();
                        p.next();
                        check_identifier(p, env, ns, id);
                        exceptions.push_back(id);
                        fingerprint = hash(fingerprint, id.hash());
                    }
                } else if (p.curr_is_identifier()) {
                    found_explicit = true;
                    while (p.curr_is_identifier()) {
                        name id = p.get_name_val();
                        p.next();
                        fingerprint = hash(fingerprint, id.hash());
                        check_identifier(p, env, ns, id);
                        if (open)
                            env = add_expr_alias(env, as+id, ns+id);
                        else
                            env = add_abbrev(p, env, as+id, ns+id);
                    }
                } else {
                    throw parser_error("invalid 'open/export' command option, "
                                       "identifier, 'hiding' or 'renaming' expected", p.pos());
                }
                if (found_explicit && !exceptions.empty())
                    throw parser_error("invalid 'open/export' command option, "
                                       "mixing explicit and implicit 'open/export' options", p.pos());
                p.check_token_next(get_rparen_tk(), "invalid 'open/export' command option, ')' expected");
            }
            if (!found_explicit) {
                if (open) {
                    env = add_aliases(env, ns, as, exceptions.size(), exceptions.data());
                } else {
                    environment new_env = env;
                    env.for_each_declaration([&](declaration const & d) {
                            if (!is_protected(env, d.get_name()) &&
                                is_prefix_of(ns, d.get_name()) &&
                                !is_exception(d.get_name(), ns, exceptions.size(), exceptions.data())) {
                                name new_id = d.get_name().replace_prefix(ns, as);
                                if (!new_id.is_anonymous())
                                    new_env = add_abbrev(p, new_env, new_id, d.get_name());
                            }
                        });
                    env = new_env;
                }
            }
        }
        if (!is_next_metaclass_tk(p) && !p.curr_is_identifier())
            break;
    }
    return update_fingerprint(env, fingerprint);
}
static environment open_cmd(parser & p) { return open_export_cmd(p, true); }
static environment export_cmd(parser & p) { return open_export_cmd(p, false); }

static environment override_cmd(parser & p) {
    environment env = p.env();
    while (p.curr_is_identifier()) {
        auto pos   = p.pos();
        name ns    = p.check_id_next("invalid 'override' command, identifier expected");
        optional<name> real_ns = to_valid_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        bool persistent = false;
        env = override_notation(env, ns, persistent);
        env = overwrite_aliases(env, ns, name());
        env = update_fingerprint(env, ns.hash());
    }
    return env;
}

static environment erase_cache_cmd(parser & p) {
    name n = p.check_id_next("invalid #erase_cache command, identifier expected");
    p.erase_cached_definition(n);
    return p.env();
}

static environment projections_cmd(parser & p) {
    name n = p.check_id_next("invalid #projections command, identifier expected");
    if (p.curr_is_token(get_dcolon_tk())) {
        p.next();
        buffer<name> proj_names;
        while (p.curr_is_identifier()) {
            proj_names.push_back(n + p.get_name_val());
            p.next();
        }
        return mk_projections(p.env(), n, proj_names);
    } else {
        return mk_projections(p.env(), n);
    }
}

static environment telescope_eq_cmd(parser & p) {
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    buffer<expr> t;
    while (is_pi(e)) {
        expr local = mk_local(p.mk_fresh_name(), binding_name(e), binding_domain(e), binder_info());
        t.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    auto tc = mk_type_checker(p.env(), p.mk_ngen());
    buffer<expr> eqs;
    mk_telescopic_eq(*tc, t, eqs);
    for (expr const & eq : eqs) {
        regular(p.env(), p.ios()) << local_pp_name(eq) << " : " << mlocal_type(eq) << "\n";
        tc->check(mlocal_type(eq), ls);
    }
    return p.env();
}

static environment local_cmd(parser & p) {
    if (p.curr_is_token_or_id(get_attribute_tk())) {
        p.next();
        return local_attribute_cmd(p);
    } else if (p.curr_is_token(get_abbreviation_tk())) {
        p.next();
        return local_abbreviation_cmd(p);
    } else {
        return local_notation_cmd(p);
    }
}

static environment help_cmd(parser & p) {
    flycheck_information info(p.regular_stream());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.regular_stream() << "help result:\n";
    }
    if (p.curr_is_token_or_id(get_options_tk())) {
        p.next();
        for (auto odecl : get_option_declarations()) {
            auto opt = odecl.second;
            regular(p.env(), p.ios())
                << "  " << opt.get_name() << " (" << opt.kind() << ") "
                << opt.get_description() << " (default: " << opt.get_default_value() << ")" << endl;
        }
    } else if (p.curr_is_token_or_id(get_commands_tk())) {
        p.next();
        buffer<name> ns;
        cmd_table const & cmds = p.cmds();
        cmds.for_each([&](name const & n, cmd_info const &) {
                ns.push_back(n);
            });
        std::sort(ns.begin(), ns.end());
        for (name const & n : ns) {
            regular(p.env(), p.ios())
                << "  " << n << ": " << cmds.find(n)->get_descr() << endl;
        };
    } else {
        p.regular_stream()
            << "help options  : describe available options\n"
            << "help commands : describe available commands\n";
    }
    return p.env();
}

static environment init_quotient_cmd(parser & p) {
    if (!(p.env().prop_proof_irrel() && p.env().impredicative()))
        throw parser_error("invalid init_quotient command, this command is only available for kernels containing an impredicative and proof irrelevant Prop", p.cmd_pos());
    return module::declare_quotient(p.env());
}

static environment init_hits_cmd(parser & p) {
    if (p.env().prop_proof_irrel() || p.env().impredicative())
        throw parser_error("invalid init_hits command, this command is only available for proof relevant and predicative kernels", p.cmd_pos());
    return module::declare_hits(p.env());
}

void init_cmd_table(cmd_table & r) {
    add_cmd(r, cmd_info("open",          "create aliases for declarations, and use objects defined in other namespaces",
                        open_cmd));
    add_cmd(r, cmd_info("export",        "create abbreviations for declarations, "
                        "and export objects defined in other namespaces", export_cmd));
    add_cmd(r, cmd_info("override",      "override notation declarations using the ones defined in the given namespace",
                        override_cmd));
    add_cmd(r, cmd_info("set_option",    "set configuration option", set_option_cmd));
    add_cmd(r, cmd_info("exit",          "exit", exit_cmd));
    add_cmd(r, cmd_info("print",         "print a string", print_cmd));
    add_cmd(r, cmd_info("section",       "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace",     "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",           "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("check",         "type check given expression, and display its type", check_cmd));
    add_cmd(r, cmd_info("eval",          "evaluate given expression", eval_cmd));
    add_cmd(r, cmd_info("find_decl",     "find definitions and/or theorems", find_cmd));
    add_cmd(r, cmd_info("local",         "define local attributes or notation", local_cmd));
    add_cmd(r, cmd_info("help",          "brief description of available commands and options", help_cmd));
    add_cmd(r, cmd_info("init_quotient", "initialize quotient type computational rules", init_quotient_cmd));
    add_cmd(r, cmd_info("init_hits",     "initialize builtin HITs", init_hits_cmd));
    add_cmd(r, cmd_info("#erase_cache",  "erase cached definition (for debugging purposes)", erase_cache_cmd));
    add_cmd(r, cmd_info("#projections",  "generate projections for inductive datatype (for debugging purposes)", projections_cmd));
    add_cmd(r, cmd_info("#telescope_eq", "(for debugging purposes)", telescope_eq_cmd));
    register_decl_cmds(r);
    register_inductive_cmd(r);
    register_structure_cmd(r);
    register_migrate_cmd(r);
    register_notation_cmds(r);
    register_begin_end_cmds(r);
    register_tactic_hint_cmd(r);
}

static cmd_table * g_cmds = nullptr;

cmd_table get_builtin_cmds() {
    return *g_cmds;
}

void initialize_builtin_cmds() {
    g_cmds = new cmd_table();
    init_cmd_table(*g_cmds);
}

void finalize_builtin_cmds() {
    delete g_cmds;
}
}
