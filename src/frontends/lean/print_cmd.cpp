/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "kernel/quotient/quotient.h"
#include "kernel/hits/hits.h"
#include "library/util.h"
#include "library/class.h"
#include "library/aliases.h"
#include "library/flycheck.h"
#include "library/light_lt_manager.h"
#include "library/pp_options.h"
#include "library/coercion.h"
#include "library/scoped_ext.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/attribute_manager.h"
#include "library/user_recursors.h"
#include "library/relation_manager.h"
#include "library/noncomputable.h"
#include "library/unification_hint.h"
#include "library/defeq_simp_lemmas.h"
#include "library/definitional/projection.h"
#include "library/blast/blast.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/blast/backward/backward_lemmas.h"
#include "library/blast/forward/forward_lemmas.h"
#include "library/blast/forward/pattern.h"
#include "library/blast/grinder/intro_elim_lemmas.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/structure_cmd.h"

namespace lean {
static void print_coercions(parser & p, optional<name> const & C) {
    environment const & env = p.env();
    options opts = p.regular_stream().get_options();
    opts = opts.update(get_pp_coercions_name(), true);
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

static environment print_axioms(parser & p) {
    if (p.curr_is_identifier()) {
        name c = p.check_constant_next("invalid 'print axioms', constant expected");
        environment new_env = p.reveal_all_theorems();
        print_axioms_deps(p.env(), p.regular_stream())(c);
        return new_env;
    } else {
        bool has_axioms = false;
        environment const & env = p.env();
        env.for_each_declaration([&](declaration const & d) {
                name const & n = d.get_name();
                if (!d.is_definition() && !env.is_builtin(n) && !p.in_theorem_queue(n)) {
                    p.regular_stream() << n << " : " << d.get_type() << endl;
                    has_axioms = true;
                }
            });
        if (!has_axioms)
            p.regular_stream() << "no axioms" << endl;
        return p.env();
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
    os = os.update_if_undef(get_pp_full_names_name(), true);
    os = os.update(get_pp_notation_name(), false);
    os = os.update(get_pp_preterm_name(), true);
    ios.set_options(os);
    optional<token_table> tt(get_token_table(p.env()));
    t.for_each([&](unsigned num, notation::transition const * ts, list<notation::accepting> const & overloads) {
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

static void print_patterns(parser & p, name const & n) {
    if (is_forward_lemma(p.env(), n)) {
        // we regenerate the patterns to make sure they reflect the current set of reducible constants
        try {
            blast::scope_debug scope(p.env(), p.ios());
            auto hi = blast::mk_hi_lemma(n, LEAN_DEFAULT_PRIORITY);
            if (hi.m_multi_patterns) {
                io_state_stream _out = p.regular_stream();
                options opts         = _out.get_options();
                opts                 = opts.update_if_undef(get_pp_metavar_args_name(), true);
                io_state_stream out  = _out.update_options(opts);
                out << "(multi-)patterns:\n";
                if (!is_nil(hi.m_mvars)) {
                    expr m = head(hi.m_mvars);
                    out << m << " : " << mlocal_type(m);
                    for (expr const & m : tail(hi.m_mvars)) {
                        out << ", " << m << " : " << mlocal_type(m);
                    }
                }
                out << "\n";
                for (multi_pattern const & mp : hi.m_multi_patterns) {
                    out << "{";
                    bool first = true;
                    for (expr const & p : mp) {
                        if (first) first = false; else out << ", ";
                        out << p;
                    }
                    out << "}\n";
                }
            }
        } catch (exception & ex) {
            p.display_error(ex);
        }
    }
}

static name to_user_name(environment const & env, name const & n) {
    if (auto r = hidden_to_user_name(env, n))
        return *r;
    else
        return n;
}

static void print_definition(parser const & p, name const & n, pos_info const & pos) {
    environment const & env = p.env();
    declaration d = env.get(n);
    io_state_stream out = p.regular_stream();
    options opts        = out.get_options();
    opts                = opts.update_if_undef(get_pp_beta_name(), false);
    io_state_stream new_out = out.update_options(opts);
    if (d.is_axiom())
        throw parser_error(sstream() << "invalid 'print definition', theorem '" << to_user_name(env, n)
                           << "' is not available (suggestion: use command 'reveal " << to_user_name(env, n) << "')", pos);
    if (!d.is_definition())
        throw parser_error(sstream() << "invalid 'print definition', '" << to_user_name(env, n) << "' is not a definition", pos);
    new_out << d.get_value() << endl;
}

static void print_attributes(parser const & p, name const & n) {
    environment const & env = p.env();
    io_state_stream out = p.regular_stream();
    buffer<char const *> attrs;
    get_attributes(attrs);
    for (char const * attr : attrs) {
        if (strcmp(attr, "semireducible") == 0)
            continue;
        if (has_attribute(env, attr, n)) {
            out << " " << get_attribute_token(attr);
            switch (get_attribute_kind(attr)) {
            case attribute_kind::Default:
                break;
            case attribute_kind::Prioritized: {
                unsigned prio = get_attribute_prio(env, attr, n);
                if (prio != LEAN_DEFAULT_PRIORITY)
                    out << " [priority " << prio << "]";
                break;
            }
            case attribute_kind::Parametric:
            case attribute_kind::OptParametric:
                out << " " << get_attribute_param(env, attr, n) << "]";
                break;
            case attribute_kind::MultiParametric: {
                list<unsigned> ps = get_attribute_params(env, attr, n);
                for (auto p : ps) {
                    out << " " << p;
                }
                out << "]";
                break;
            }}
        }
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
        << "  num. minors:              " << info.get_num_minors() << "\n"
        << "  recursive:                " << info.is_recursive() << "\n"
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
    out << kind << " " << to_user_name(p.env(), d.get_name());
    print_attributes(p, d.get_name());
    out << " : " << d.get_type();
    if (is_def)
        out << " :=";
    out << "\n";
    return true;
}

bool print_id_info(parser & p, name const & id, bool show_value, pos_info const & pos) {
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
                                out << "'" << to_user_name(env, d.get_name()) << "' is still in the theorem queue, use command 'reveal "
                                    << to_user_name(env, d.get_name()) << "' to access its definition.\n";
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
                print_patterns(p, c);
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

static void print_unification_hints(parser & p) {
    io_state_stream out = p.regular_stream();
    unification_hints hints;
    name ns;
    if (p.curr_is_identifier()) {
        ns = p.get_name_val();
        p.next();
        hints = get_unification_hints(p.env(), ns);
    } else {
        hints = get_unification_hints(p.env());
    }
    format header;
    if (!ns.is_anonymous())
        header = format(" at namespace '") + format(ns) + format("'");
    out << pp_unification_hints(hints, out.get_formatter(), header);
}

static void print_defeq_lemmas(parser & p) {
    io_state_stream out = p.regular_stream();
    defeq_simp_lemmas lemmas;
    name ns;
    if (p.curr_is_identifier()) {
        ns = p.get_name_val();
        p.next();
        lemmas = get_defeq_simp_lemmas(p.env(), ns);
    } else {
        lemmas = get_defeq_simp_lemmas(p.env());
    }
    format header;
    if (!ns.is_anonymous())
        header = format(" at namespace '") + format(ns) + format("'");
    out << pp_defeq_simp_lemmas(lemmas, out.get_formatter(), header);
}

static void print_simp_rules(parser & p) {
    io_state_stream out = p.regular_stream();
    blast::scope_debug scope(p.env(), p.ios());
    blast::simp_lemmas s;
    name ns;
    if (p.curr_is_identifier()) {
        ns = p.get_name_val();
        p.next();
        s = blast::get_simp_lemmas(ns);
    } else {
        s = blast::get_simp_lemmas();
    }
    format header;
    if (!ns.is_anonymous())
        header = format(" at namespace '") + format(ns) + format("'");
    out << s.pp_simp(out.get_formatter(), header);
}

static void print_congr_rules(parser & p) {
    io_state_stream out = p.regular_stream();
    blast::scope_debug scope(p.env(), p.ios());
    blast::simp_lemmas s = blast::get_simp_lemmas();
    out << s.pp_congr(out.get_formatter());
}

static void print_light_rules(parser & p) {
    io_state_stream out = p.regular_stream();
    light_rule_set lrs = get_light_rule_set(p.env());
    out << lrs;
}

static void print_elim_lemmas(parser & p) {
    buffer<name> lemmas;
    get_elim_lemmas(p.env(), lemmas);
    for (auto n : lemmas)
        p.regular_stream() << n << "\n";
}

static void print_intro_lemmas(parser & p) {
    io_state_stream out = p.regular_stream();
    buffer<name> lemmas;
    get_intro_lemmas(p.env(), lemmas);
    for (auto n : lemmas)
        out << n << "\n";
}

static void print_backward_lemmas(parser & p) {
    io_state_stream out = p.regular_stream();
    buffer<name> lemmas;
    get_backward_lemmas(p.env(), lemmas);
    for (auto n : lemmas)
        out << n << "\n";
}

static void print_no_patterns(parser & p) {
    io_state_stream out = p.regular_stream();
    auto s = get_no_patterns(p.env());
    buffer<name> ns;
    s.to_buffer(ns);
    std::sort(ns.begin(), ns.end());
    for (unsigned i = 0; i < ns.size(); i++) {
        if (i > 0) out << ", ";
        out << ns[i];
    }
    out << "\n";
}

static void print_aliases(parser const & p) {
    io_state_stream out = p.regular_stream();
    for_each_expr_alias(p.env(), [&](name const & n, list<name> const & as) {
            out << n << " -> {";
            bool first = true;
            for (name const & a : as) {
                if (first) first = false; else out << ", ";
                out << a;
            }
            out << "}\n";
        });
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
        opts = opts.update(get_pp_notation_name(), false);
        out.update_options(opts) << e << endl;
    } else if (p.curr_is_token_or_id(get_no_pattern_attr_tk())) {
        p.next();
        print_no_patterns(p);
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
                throw parser_error(sstream() << "invalid 'print definition', '" << to_user_name(p.env(), c) << "' is not a definition", pos);
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
    } else if (p.curr_is_token_or_id(get_aliases_tk())) {
        p.next();
        print_aliases(p);
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
        return print_axioms(p);
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
    } else if (p.curr_is_token(get_unify_attr_tk())) {
        p.next();
        print_unification_hints(p);
    } else if (p.curr_is_token(get_defeq_attr_tk())) {
        p.next();
        print_defeq_lemmas(p);
    } else if (p.curr_is_token(get_simp_attr_tk())) {
        p.next();
        print_simp_rules(p);
    } else if (p.curr_is_token(get_intro_bang_attr_tk())) {
        p.next();
        print_intro_lemmas(p);
    } else if (p.curr_is_token(get_elim_attr_tk())) {
        p.next();
        print_elim_lemmas(p);
    } else if (p.curr_is_token(get_congr_attr_tk())) {
        p.next();
        print_congr_rules(p);
    } else if (p.curr_is_token(get_light_attr_tk())) {
        p.next();
        p.check_token_next(get_rbracket_tk(), "invalid 'print [light]', ']' expected");
        print_light_rules(p);
    } else if (p.curr_is_token(get_intro_attr_tk())) {
        p.next();
        print_backward_lemmas(p);
    } else if (print_polymorphic(p)) {
    } else {
        throw parser_error("invalid print command", p.pos());
    }
    return p.env();
}
}
