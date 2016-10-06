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
#include "library/util.h"
#include "library/class.h"
#include "library/aliases.h"
#include "library/flycheck.h"
#include "library/pp_options.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/attribute_manager.h"
#include "library/user_recursors.h"
#include "library/noncomputable.h"
#include "library/type_context.h"
#include "library/unification_hint.h"
#include "library/reducible.h"
#include "library/rfl_lemmas.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/simplifier/simp_lemmas.h"
#include "library/tactic/simplifier/simp_extensions.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/structure_cmd.h"

namespace lean {
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
        type_context tc(new_env, p.get_options());
        auto out = regular(new_env, p.ios(), tc);
        print_axioms_deps(p.env(), out)(c);
        return new_env;
    } else {
        bool has_axioms = false;
        environment const & env = p.env();
        type_context tc(env, p.get_options());
        auto out = regular(env, p.ios(), tc);
        env.for_each_declaration([&](declaration const & d) {
                name const & n = d.get_name();
                if (!d.is_definition() && !env.is_builtin(n) && d.is_trusted()) {
                    out << n << " : " << d.get_type() << endl;
                    has_axioms = true;
                }
            });
        if (!has_axioms)
            out << "no axioms" << endl;
        return p.env();
    }
}

static void print_prefix(parser & p) {
    name prefix = p.check_id_next("invalid 'print prefix' command, identifier expected");
    environment const & env = p.env();
    buffer<declaration> to_print;
    type_context tc(env, p.get_options());
    auto out = regular(env, p.ios(), tc);
    env.for_each_declaration([&](declaration const & d) {
            if (is_prefix_of(prefix, d.get_name())) {
                to_print.push_back(d);
            }
        });
    std::sort(to_print.begin(), to_print.end(), [](declaration const & d1, declaration const & d2) { return d1.get_name() < d2.get_name(); });
    for (declaration const & d : to_print) {
        out << d.get_name() << " : " << d.get_type() << endl;
    }
    if (to_print.empty())
        out << "no declaration starting with prefix '" << prefix << "'" << endl;
}

static void print_fields(parser const & p, name const & S, pos_info const & pos) {
    environment const & env = p.env();
    if (!is_structure(env, S))
        throw parser_error(sstream() << "invalid 'print fields' command, '" << S << "' is not a structure", pos);
    buffer<name> field_names;
    get_structure_fields(env, S, field_names);
    type_context tc(env, p.get_options());
    auto out = regular(env, p.ios(), tc);
    for (name const & field_name : field_names) {
        declaration d = env.get(field_name);
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

static bool print_parse_table(parser const & p, parse_table const & t, bool nud, buffer<name> const & tokens, bool tactic_table = false) {
    bool found = false;
    io_state ios = p.ios();
    options os   = ios.get_options();
    os = os.update_if_undef(get_pp_full_names_name(), true);
    os = os.update(get_pp_notation_name(), false);
    os = os.update(get_pp_preterm_name(), true);
    ios.set_options(os);
    type_context tc(p.env(), p.get_options());
    io_state_stream out = regular(p.env(), ios, tc);
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
        p.ios().get_regular_stream() << "no notation" << std::endl;
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
                type_context tc(p.env(), opts);
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

static void print_definition(parser const & p, name const & n, pos_info const & pos) {
    environment const & env = p.env();
    declaration d = env.get(n);
    options opts        = p.get_options();
    opts                = opts.update_if_undef(get_pp_beta_name(), false);
    io_state ios(p.ios(), opts);
    type_context tc(env, opts);
    io_state_stream out = regular(env, ios, tc);
    if (d.is_axiom())
        throw parser_error(sstream() << "invalid 'print definition', theorem '" << to_user_name(env, n)
                           << "' is not available (suggestion: use command 'reveal " << to_user_name(env, n) << "')", pos);
    if (!d.is_definition())
        throw parser_error(sstream() << "invalid 'print definition', '" << to_user_name(env, n) << "' is not a definition", pos);
    out << d.get_value() << endl;
}

static void print_attributes(parser const & p, name const & n) {
    environment const & env = p.env();
    std::ostream & out = p.ios().get_regular_stream();
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
                out << "attribute [";
                first = false;
            } else {
                out << ", ";
            }
            out << attr->get_name();
            data->print(out);
            unsigned prio = attr->get_prio(env, n);
            if (prio != LEAN_DEFAULT_PRIORITY)
                out << ", priority " << prio;
        }
    }
    if (!first)
        out << "]\n";
}

static void print_inductive(parser const & p, name const & n, pos_info const & pos) {
    environment const & env = p.env();
    type_checker tc(env);
    io_state_stream out = regular(env, p.ios(), tc);
    if (auto idecl = inductive::is_inductive_decl(env, n)) {
        level_param_names ls = idecl->m_level_params;
        print_attributes(p, n);
        if (is_structure(env, n))
            out << "structure";
        else
            out << "inductive";
        out << " " << n;
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
    std::ostream & out = p.ios().get_regular_stream();
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
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc);
    print_attributes(p, d.get_name());
    if (is_protected(p.env(), d.get_name()))
        out << "protected ";
    if (d.is_definition() && is_marked_noncomputable(p.env(), d.get_name()))
        out << "noncomputable ";
    out << kind << " " << to_user_name(p.env(), d.get_name());
    out.update_options(out.get_options().update((name {"pp", "binder_types"}), true)) << " : " << d.get_type();
    if (is_def)
        out << " :=";
    out << "\n";
    return true;
}

bool print_id_info(parser & p, name const & id, bool show_value, pos_info const & pos) {
    // declarations
    try {
        environment const & env = p.env();
        type_checker tc(env);
        auto out = regular(env, p.ios(), tc);
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
                    } else if (d.is_axiom()) {
                        print_constant(p, "axiom", d);
                    } else {
                        print_constant(p, "constant", d);
                    }
                } else if (d.is_definition()) {
                    print_constant(p, "definition", d, show_value);
                    if (show_value)
                        print_definition(p, c, pos);
                }
                // print_patterns(p, c);
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
        auto decls = get_option_declarations();
        bool found = false;
        decls.for_each([&](name const &, option_declaration const & opt) {
                if (found) return;
                if (opt.get_name() == id || opt.get_name() == name("lean") + id) {
                    out << "option  " << opt.get_name() << " (" << opt.kind() << ") "
                        << opt.get_description() << " (default: " << opt.get_default_value() << ")" << endl;
                    found = true;
                }
            });
        if (found) return true;
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

static void print_unification_hints(parser & p) {
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc);
    out << pp_unification_hints(get_unification_hints(p.env()), out.get_formatter());
}

static void print_rfl_lemmas(parser & p) {
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc);
    out << pp_rfl_lemmas(get_rfl_lemmas(p.env()), out.get_formatter());
}

static void print_simp_rules(parser & p) {
    type_context aux_tctx(p.env(), p.get_options());
    name attr = p.check_id_next("invalid 'print [simp]' command, identifier expected");
    buffer<name> attrs;
    attrs.push_back(attr);
    buffer<name> no_congr;
    simp_lemmas slss = get_simp_lemmas(aux_tctx, attrs, no_congr);
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc);
    out << slss.pp_simp(out.get_formatter());
}

static void print_congr_rules(parser & p) {
    type_context aux_tctx(p.env(), p.get_options());
    name attr = p.check_id_next("invalid 'print [congr]' command, identifier expected");
    buffer<name> no_simp;
    buffer<name> attrs;
    attrs.push_back(attr);
    simp_lemmas slss = get_simp_lemmas(aux_tctx, no_simp, attrs);
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc);
    out << slss.pp_congr(out.get_formatter());
}

static void print_simp_extensions(parser & p) {
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc);
    out << pp_simp_extensions(p.env());
}

#if 0
static void print_light_rules(parser & p) {
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc);
    light_rule_set lrs = get_light_rule_set(p.env());
    out << lrs;
}
#endif

static void print_aliases(parser const & p) {
    std::ostream & out = p.ios().get_regular_stream();
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

static void print_key_equivalences(parser & p) {
    std::ostream & out = p.ios().get_regular_stream();
    for_each_key_equivalence(p.env(), [&](buffer<name> const & ns) {
            out << "[";
            for (unsigned i = 0; i < ns.size(); i++) {
                if (i > 0) out << ", ";
                out << ns[i];
            }
            out << "]\n";
        });
}

static void print_attribute(parser & p, attribute const & attr) {
    buffer<name> instances;
    attr.get_instances(p.env(), instances);

    // oldest first
    unsigned i = instances.size();
    while (i > 0) {
        --i;
        p.ios().get_regular_stream() << instances[i] << "\n";
    }
}

environment print_cmd(parser & p) {
    flycheck_information info(p.ios());
    environment const & env = p.env();
    type_checker tc(env);
    auto out = regular(env, p.ios(), tc);
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        out << "print result:\n";
    }
    if (p.curr() == scanner::token_kind::String) {
        out << p.get_str_val() << endl;
        p.next();
    } else if (p.curr_is_token_or_id(get_raw_tk())) {
        p.next();
        expr e = p.parse_expr();
        options opts = out.get_options();
        opts = opts.update(get_pp_notation_name(), false);
        out.update_options(opts) << e << endl;
    } else if (p.curr_is_token_or_id(get_options_tk())) {
        p.next();
        out << p.ios().get_options() << endl;
    } else if (p.curr_is_token_or_id(get_trust_tk())) {
        p.next();
        out << "trust level: " << p.env().trust_lvl() << endl;
    } else if (p.curr_is_token_or_id(get_key_equivalences_tk())) {
        p.next();
        print_key_equivalences(p);
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
                out << "\n";
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
        print_prefix(p);
    } else if (p.curr_is_token_or_id(get_aliases_tk())) {
        p.next();
        print_aliases(p);
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
    } else if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        auto pos = p.pos();
        auto name = p.check_id_next("invalid attribute declaration, identifier expected");
        p.check_token_next(get_rbracket_tk(), "invalid 'print [<attr>]', ']' expected");

        if (name == "recursor")
            print_recursor_info(p);
        else if (name == "unify")
            print_unification_hints(p);
        else if (name == "defeq")
            print_rfl_lemmas(p);
        else if (name == "simp")
            print_simp_rules(p);
        else if (name == "simp_ext")
            print_simp_extensions(p);
        else if (name == "congr")
            print_congr_rules(p);
        else if (name == "light") {
            // print_light_rules(p);
        } else {
            if (!is_attribute(p.env(), name))
                throw parser_error(sstream() << "unknown attribute [" << name << "]", pos);
            auto const & attr = get_attribute(p.env(), name);
            print_attribute(p, attr);
        }
    } else if (print_polymorphic(p)) {
    } else {
        throw parser_error("invalid print command", p.pos());
    }
    return p.env();
}
}
