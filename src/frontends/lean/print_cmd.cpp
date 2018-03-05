/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "library/trace.h"
#include "library/sorry.h"
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "kernel/quotient/quotient.h"
#include "library/util.h"
#include "library/class.h"
#include "library/aliases.h"
#include "library/pp_options.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/attribute_manager.h"
#include "library/user_recursors.h"
#include "library/noncomputable.h"
#include "library/type_context.h"
#include "library/unification_hint.h"
#include "library/reducible.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/kabstract.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/info_manager.h"

// TODO(gabriel): make print command async

namespace lean {
struct print_axioms_deps {
    environment     m_env;
    io_state_stream m_ios;
    name_set        m_visited;
    bool            m_use_axioms;
    bool            m_used_sorry;
    print_axioms_deps(environment const & env, io_state_stream const & ios):
        m_env(env), m_ios(ios), m_use_axioms(false), m_used_sorry(false) {}

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
                if (is_sorry(e) && !m_used_sorry) {
                    m_used_sorry = true;
                    m_ios << "[sorry]" << "\n";
                }
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

static void print_axioms(parser & p, message_builder & out) {
    if (p.curr_is_identifier()) {
        name c = p.check_constant_next("invalid '#print axioms', constant expected");
        auto env = p.env();
        type_context_old tc(env, p.get_options());
        auto new_out = io_state_stream(env, p.ios(), tc, out.get_text_stream().get_channel());
        print_axioms_deps(env, new_out)(c);
    } else {
        bool has_axioms = false;
        p.env().for_each_declaration([&](declaration const & d) {
                name const & n = d.get_name();
                if (!d.is_definition() && !p.env().is_builtin(n) && d.is_trusted()) {
                    out << n << " : " << d.get_type() << endl;
                    has_axioms = true;
                }
            });
        if (!has_axioms)
            out << "no axioms" << endl;
    }
}

static void print_prefix(parser & p, message_builder & out) {
    name prefix = p.check_id_next("invalid '#print prefix' command, identifier expected");
    buffer<declaration> to_print;
    p.env().for_each_declaration([&](declaration const & d) {
            if (is_prefix_of(prefix, d.get_name())) {
                to_print.push_back(d);
            }
        });
    std::sort(to_print.begin(), to_print.end(), [](declaration const & d1, declaration const & d2) { return d1.get_name() < d2.get_name(); });
    for (declaration const & d : to_print) {
        out << d.get_name() << " : " << d.get_type() << "\n";
    }
    if (to_print.empty())
        out << "no declaration starting with prefix '" << prefix << "'\n";
}

static void print_fields(parser const & p, message_builder & out, name const & S, pos_info const & pos) {
    environment const & env = p.env();
    if (!is_structure(env, S))
        throw parser_error(sstream() << "invalid '#print fields' command, '" << S << "' is not a structure", pos);
    for (name const & field_name : get_structure_fields(env, S)) {
        declaration d = env.get(S + field_name);
        out << d.get_name() << " : " << d.get_type() << endl;
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

static bool print_parse_table(parser const & p, message_builder & rep, parse_table const & t, bool nud, buffer<name> const & tokens, bool tactic_table = false) {
    bool found = false;
    options os   = rep.get_text_stream().get_options();
    os = os.update_if_undef(get_pp_full_names_name(), true);
    os = os.update(get_pp_notation_name(), false);
    os = os.update(get_pp_preterm_name(), true);
    auto out = rep.get_text_stream().update_options(os);
    optional<token_table> tt(get_token_table(p.env()));
    t.for_each([&](unsigned num, notation::transition const * ts, list<notation::accepting> const & overloads) {
            if (uses_some_token(num, ts, tokens)) {
                if (tactic_table)
                    out << "tactic notation ";
                found = true;
                notation::display(out, num, ts, overloads, nud, tt);
            }
        });
    return found;
}

static void print_notation(parser & p, message_builder & out) {
    buffer<name> tokens;
    while (p.curr_is_keyword()) {
        tokens.push_back(p.get_token_info().token());
        p.next();
    }
    bool found = false;
    if (print_parse_table(p, out, get_nud_table(p.env()), true, tokens))
        found = true;
    if (print_parse_table(p, out, get_led_table(p.env()), false, tokens))
        found = true;
    if (!found)
        out << "no notation";
}

#if 0
static void print_patterns(parser & p, name const & n) {
    if (is_forward_lemma(p.env(), n)) {
        // we regenerate the patterns to make sure they reflect the current set of reducible constants
        try {
            blast::scope_debug scope(p.env(), p.ios());
            auto hi = blast::mk_hi_lemma(n, LEAN_DEFAULT_PRIORITY);
            if (hi.m_multi_patterns) {
                options opts         = p.get_options();
                opts                 = opts.update_if_undef(get_pp_metavar_args_name(), true);
                io_state new_ios(p.ios(), opts);
                type_context_old tc(p.env(), opts);
                io_state_stream out = regular(p.env(), new_ios, tc);
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
#endif

static name to_user_name(environment const & env, name const & n) {
    if (auto r = hidden_to_user_name(env, n))
        return *r;
    else
        return n;
}

static void print_definition(environment const & env, message_builder & out, name const & n, pos_info const & pos) {
    declaration d = env.get(n);
    if (!d.is_definition())
        throw parser_error(sstream() << "invalid '#print definition', '" << to_user_name(env, n) << "' is not a definition", pos);
    options opts        = out.get_text_stream().get_options();
    opts                = opts.update_if_undef(get_pp_beta_name(), false);
    out.get_text_stream().update_options(opts) << d.get_value() << endl;
}

static void print_attributes(parser const & p, message_builder & out, name const & n) {
    environment const & env = p.env();
    buffer<attribute const *> attrs;
    get_attributes(p.env(), attrs);
    std::sort(attrs.begin(), attrs.end(), [](attribute const * a1, attribute const * a2) {
        return a1->get_name() < a2->get_name();
    });
    bool first = true;
    for (auto attr : attrs) {
        if (attr->get_name() == "reducibility")
            continue;
        if (auto data = attr->get_untyped(env, n)) {
            if (first) {
                out << "@[";
                first = false;
            } else {
                out << ", ";
            }
            out << attr->get_name();
            data->print(out.get_text_stream().get_stream());
            unsigned prio = attr->get_prio(env, n);
            if (prio != LEAN_DEFAULT_PRIORITY)
                out << ", priority " << prio;
        }
    }
    if (!first)
        out << "]\n";
}

static void print_inductive(parser const & p, message_builder & out, name const & n, pos_info const & pos) {
    environment const & env = p.env();
    if (auto idecl = inductive::is_inductive_decl(env, n)) {
        level_param_names ls = idecl->m_level_params;
        print_attributes(p, out, n);
        if (is_structure(env, n))
            out << "structure";
        else
            out << "inductive";
        out << " " << n;
        out << " : " << env.get(n).get_type() << "\n";
        if (is_structure(env, n)) {
            out << "fields:\n";
            print_fields(p, out, n, pos);
        } else {
            out << "constructors:\n";
            buffer<name> constructors;
            get_intro_rule_names(env, n, constructors);
            for (name const & c : constructors) {
                out << c << " : " << env.get(c).get_type() << "\n";
            }
        }
    } else {
        throw parser_error(sstream() << "invalid '#print inductive', '" << n << "' is not an inductive declaration", pos);
    }
}

static void print_recursor_info(parser & p, message_builder & out) {
    name c = p.check_constant_next("invalid '#print [recursor]', constant expected");
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

static bool print_constant(parser const & p, message_builder & out, char const * kind, declaration const & d, bool is_def = false) {
    type_checker tc(p.env());
    print_attributes(p, out, d.get_name());
    if (is_protected(p.env(), d.get_name()))
        out << "protected ";
    if (d.is_definition() && is_marked_noncomputable(p.env(), d.get_name()))
        out << "noncomputable ";
    if (!d.is_trusted())
        out << "meta ";
    out << kind << " " << to_user_name(p.env(), d.get_name());
    out.get_text_stream().update_options(out.get_text_stream().get_options().update((name {"pp", "binder_types"}), true))
            << " : " << d.get_type();
    if (is_def)
        out << " :=";
    out << "\n";
    return true;
}

void print_id_info(parser & p, message_builder & out, name const & id, bool show_value, pos_info const & pos) {
    environment const & env = p.env();
    bool found = false;

    // declarations
    list<name> cs;
    try {
        cs = p.to_constants(id, "", pos);
        found = true;
    } catch (parser_error) {}
    bool first = true;
    for (name const & c : cs) {
        if (first) first = false; else out << "\n";
        declaration const & d = env.get(c);
        if (d.is_theorem()) {
            print_constant(p, out, "theorem", d, show_value);
            try {
                if (show_value)
                    print_definition(env, out, c, pos);
            } catch (std::exception & ex) {
                out << "[incorrect proof]\n";
                bool use_pos = false;
                out.set_exception(ex, use_pos);
            }
        } else if (d.is_axiom() || d.is_constant_assumption()) {
            if (inductive::is_inductive_decl(env, c)) {
                print_inductive(p, out, c, pos);
            } else if (inductive::is_intro_rule(env, c)) {
                print_constant(p, out, "constructor", d);
            } else if (inductive::is_elim_rule(env, c)) {
                print_constant(p, out, "eliminator", d);
            } else if (is_quotient_decl(env, c)) {
                print_constant(p, out, "builtin-quotient-type-constant", d);
            } else if (d.is_axiom()) {
                print_constant(p, out, "axiom", d);
            } else {
                print_constant(p, out, "constant", d);
            }
        } else if (d.is_definition()) {
            print_constant(p, out, "def", d, show_value);
            if (show_value)
                print_definition(env, out, c, pos);
        }
        // print_patterns(p, c);
    }

    // add to info_manager when not overloaded
    if (auto c = head_opt(cs))
        if (!tail(cs))
            if (auto infom = get_global_info_manager()) {
                infom->add_const_info(p.env(), pos, *c);
            }

    if (found) return;

    // variables and parameters
    if (expr const * type = p.get_local(id)) {
        if (is_local(*type)) {
            if (p.is_local_variable(*type)) {
                out << "variable " << id << " : " << mlocal_type(*type) << "\n";
            } else {
                out << "parameter " << id << " : " << mlocal_type(*type) << "\n";
            }
            return;
        }
    }

    // options
    get_option_declarations().for_each([&](name const &, option_declaration const & opt) {
            if (found) return;
            if (opt.get_name() == id || opt.get_name() == name("lean") + id) {
                out << "option  " << opt.get_name() << " (" << opt.kind() << ") "
                    << opt.get_description() << " (default: " << opt.get_default_value() << ")" << endl;
                found = true;
            }
        });

    if (!found) throw parser_error(sstream() << "unknown identifier " << id, p.pos());
}

bool print_token_info(parser const & p, message_builder & out, name const & tk) {
    buffer<name> tokens;
    tokens.push_back(tk);
    bool found = false;
    if (print_parse_table(p, out, get_nud_table(p.env()), true, tokens)) {
        found = true;
    }
    if (print_parse_table(p, out, get_led_table(p.env()), false, tokens)) {
        found = true;
    }
    return found;
}

void print_polymorphic(parser & p, message_builder & out) {
    auto pos = p.pos();

    // notation
    if (p.curr_is_keyword()) {
        name tk = p.get_token_info().token();
        if (print_token_info(p, out, tk)) {
            p.next();
            return;
        }
    }

    name id = p.check_id_next("invalid #print command", break_at_pos_exception::token_context::expr);
    bool show_value = true;
    print_id_info(p, out, id, show_value, pos);
}

static void print_unification_hints(parser & p, message_builder & out) {
    out << pp_unification_hints(get_unification_hints(p.env()), out.get_formatter());
}

static void print_simp_rules(parser & p, message_builder & out) {
    name attr = p.check_id_next("invalid '#print [simp]' command, identifier expected");
    simp_lemmas slss = get_simp_lemmas(p.env(), attr);
    out << slss.pp_simp(out.get_formatter());
}

static void print_congr_rules(parser & p, message_builder & out) {
    name attr = p.check_id_next("invalid '#print [congr]' command, identifier expected");
    simp_lemmas slss = get_simp_lemmas(p.env(), attr);
    out << slss.pp_congr(out.get_formatter());
}

static void print_aliases(parser const & p, message_builder & out) {
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

static void print_key_equivalences(parser & p, message_builder & out) {
    for_each_key_equivalence(p.env(), [&](buffer<name> const & ns) {
            out << "[";
            for (unsigned i = 0; i < ns.size(); i++) {
                if (i > 0) out << ", ";
                out << ns[i];
            }
            out << "]\n";
        });
}

static void print_attribute(parser & p, message_builder & out, attribute const & attr) {
    buffer<name> instances;
    attr.get_instances(p.env(), instances);

    // oldest first
    unsigned i = instances.size();
    while (i > 0) {
        --i;
        out << instances[i] << "\n";
    }
}

environment print_cmd(parser & p) {
    // Fallbacks are handled via exceptions.
    auto _ = p.no_error_recovery_scope();

    auto out = p.mk_message(p.cmd_pos(), INFORMATION);
    out.set_caption("print result");
    auto env = p.env();
    if (p.curr() == token_kind::String) {
        out << p.get_str_val() << endl;
        p.next();
    } else if (p.curr_is_token_or_id(get_raw_tk())) {
        p.next();
        auto _ = p.error_recovery_scope(true);
        expr e = p.parse_expr();
        options opts = out.get_text_stream().get_options();
        opts = opts.update(get_pp_notation_name(), false);
        out.get_text_stream().update_options(opts) << e << endl;
    } else if (p.curr_is_token_or_id(get_options_tk())) {
        p.next();
        out << p.ios().get_options() << endl;
    } else if (p.curr_is_token_or_id(get_trust_tk())) {
        p.next();
        out << "trust level: " << p.env().trust_lvl() << endl;
    } else if (p.curr_is_token_or_id(get_key_equivalences_tk())) {
        p.next();
        print_key_equivalences(p, out);
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
        auto pos = p.pos();
        name id  = p.check_id_next("invalid '#print definition', constant expected");
        list<name> cs = p.to_constants(id, "invalid '#print definition', constant expected", pos);
        bool first = true;
        for (name const & c : cs) {
            if (first)
                first = false;
            else
                out << "\n";
            declaration const & d = p.env().get(c);
            if (d.is_theorem()) {
                print_constant(p, out, "theorem", d);
                print_definition(env, out, c, pos);
            } else if (d.is_definition()) {
                print_constant(p, out, "definition", d);
                print_definition(env, out, c, pos);
            } else {
                throw parser_error(sstream() << "invalid '#print definition', '" << to_user_name(p.env(), c) << "' is not a definition", pos);
            }
        }
    } else if (p.curr_is_token_or_id(get_instances_tk())) {
        p.next();
        name c = p.check_constant_next("invalid '#print instances', constant expected");
        for (name const & i : get_class_instances(env, c)) {
            out << i << " : " << env.get(i).get_type() << endl;
        }
    } else if (p.curr_is_token_or_id(get_classes_tk())) {
        p.next();
        buffer<name> classes;
        get_classes(env, classes);
        std::sort(classes.begin(), classes.end());
        for (name const & c : classes) {
            out << c << " : " << env.get(c).get_type() << endl;
        }
    } else if (p.curr_is_token_or_id(get_attributes_tk())) {
        p.next();
        buffer<attribute const *> attrs;
        get_attributes(p.env(), attrs);
        std::sort(attrs.begin(), attrs.end(), [](attribute const * a1, attribute const * a2) {
            return a1->get_name() < a2->get_name();
        });
        for (auto attr : attrs) {
            out << "[" << attr->get_name() << "] " << attr->get_description() << endl;
        }
    } else if (p.curr_is_token_or_id(get_prefix_tk())) {
        p.next();
        print_prefix(p, out);
    } else if (p.curr_is_token_or_id(get_aliases_tk())) {
        p.next();
        print_aliases(p, out);
    } else if (p.curr_is_token_or_id(get_axioms_tk())) {
        p.next();
        print_axioms(p, out);
    } else if (p.curr_is_token_or_id(get_fields_tk())) {
        p.next();
        auto pos = p.pos();
        name S = p.check_constant_next("invalid '#print fields' command, constant expected");
        print_fields(p, out, S, pos);
    } else if (p.curr_is_token_or_id(get_notation_tk())) {
        p.next();
        print_notation(p, out);
    } else if (p.curr_is_token_or_id(get_inductive_tk())) {
        p.next();
        auto pos = p.pos();
        name c = p.check_constant_next("invalid '#print inductive', constant expected");
        print_inductive(p, out, c, pos);
    } else if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        auto pos = p.pos();
        auto name = p.check_id_next("invalid attribute declaration, identifier expected");
        p.check_token_next(get_rbracket_tk(), "invalid '#print [<attr>]', ']' expected");

        if (name == "recursor") {
            print_recursor_info(p, out);
        } else if (name == "unify") {
            print_unification_hints(p, out);
        } else if (name == "simp") {
            print_simp_rules(p, out);
        } else if (name == "congr") {
            print_congr_rules(p, out);
        } else {
            if (!is_attribute(p.env(), name))
                throw parser_error(sstream() << "unknown attribute [" << name << "]", pos);
            auto const & attr = get_attribute(p.env(), name);
            print_attribute(p, out, attr);
        }
    } else {
        print_polymorphic(p, out);
    }
    out.set_end_pos(p.pos());
    out.report();
    return p.env();
}
}
