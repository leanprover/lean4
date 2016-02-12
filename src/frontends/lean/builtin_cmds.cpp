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
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/class.h"
#include "library/flycheck.h"
#include "library/abbreviation.h"
#include "library/user_recursors.h"
#include "library/pp_options.h"
#include "library/aux_recursors.h"
#include "library/private.h"
#include "library/fun_info_manager.h"
#include "library/congr_lemma_manager.h"
#include "library/abstract_expr_manager.h"
#include "library/definitional/projection.h"
#include "library/blast/blast.h"
#include "library/blast/simplifier/simplifier.h"
#include "compiler/preprocess_rec.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/inductive_cmd.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/print_cmd.h"
#include "frontends/lean/find_cmd.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parse_table.h"

namespace lean {
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
    auto tc = mk_type_checker(p.env());
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
        auto tc = mk_type_checker(p.env());
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

static optional<name> parse_metaclass(parser & p) {
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
        if (!is_metaclass(n) && n != get_decl_tk() && n != get_declaration_tk())
            throw parser_error(sstream() << "invalid metaclass name '[" << n << "]'", pos);
        return optional<name>(n);
    } else if (p.curr() == scanner::token_kind::CommandKeyword) {
        // Meta-classes whose name conflict with tokens of the form `[<id>]` `[<id>`
        // Example: [class] and [unfold
        name v = p.get_token_info().value();
        if (v.is_atomic() && v.is_string() && v.size() > 1 && v.get_string()[0] == '[') {
            auto pos = p.pos();
            p.next();
            std::string s(v.get_string() + 1);
            if (v.get_string()[v.size()-1] == ']')
                s.pop_back();
            name n(s);
            if (!is_metaclass(n) && n != get_decl_tk() && n != get_declaration_tk())
                throw parser_error(sstream() << "invalid metaclass name '[" << n << "]'", pos);
            if (v.get_string()[v.size()-1] != ']') {
                // Consume ']' for tokens such as `[unfold`
                p.check_token_next(get_rbracket_tk(), "invalid 'open' command, ']' expected");
            }
            return optional<name>(n);
        }
    }
    return optional<name>();
}

static void parse_metaclasses(parser & p, buffer<name> & r) {
    if (p.curr_is_token(get_sub_tk())) {
        p.next();
        buffer<name> tmp;
        get_metaclasses(tmp);
        tmp.push_back(get_decl_tk());
        while (true) {
            if (optional<name> m = parse_metaclass(p)) {
                tmp.erase_elem(*m);
                if (*m == get_declaration_tk())
                    tmp.erase_elem(get_decl_tk());
            } else {
                break;
            }
        }
        r.append(tmp);
    } else {
        while (true) {
            if (optional<name> m = parse_metaclass(p)) {
                r.push_back(*m);
            } else {
                break;
            }
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
            std::find(metacls.begin(), metacls.end(), get_decl_tk()) != metacls.end() ||
            std::find(metacls.begin(), metacls.end(), get_declaration_tk()) != metacls.end())
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
            env = mark_namespace_as_open(env, ns);
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
        expr local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), binder_info());
        t.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    auto tc = mk_type_checker(p.env());
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

static environment compile_cmd(parser & p) {
    name n = p.check_constant_next("invalid #compile command, constant expected");
    declaration d = p.env().get(n);
    buffer<name> aux_decls;
    preprocess_rec(p.env(), d, aux_decls);
    return p.env();
}

static environment accessible_cmd(parser & p) {
    environment const & env = p.env();
    unsigned total               = 0;
    unsigned accessible          = 0;
    unsigned accessible_theorems = 0;
    env.for_each_declaration([&](declaration const & d) {
            name const & n = d.get_name();
            total++;
            if ((d.is_theorem() || d.is_definition()) &&
                !is_instance(env, n) && !is_simp_lemma(env, n) && !is_congr_lemma(env, n) &&
                !is_user_defined_recursor(env, n) && !is_aux_recursor(env, n) &&
                !is_projection(env, n) && !is_private(env, n) &&
                !is_user_defined_recursor(env, n) && !is_aux_recursor(env, n) &&
                !is_subst_relation(env, n) && !is_trans_relation(env, n) &&
                !is_symm_relation(env, n) && !is_refl_relation(env, n)) {
                accessible++;
                if (d.is_theorem())
                    accessible_theorems++;
            }
        });
    p.regular_stream() << "total: " << total << ", accessible: " << accessible << ", accessible theorems: " << accessible_theorems << "\n";
    return env;
}

static void check_expr_and_print(parser & p, expr const & e) {
    environment const & env = p.env();
    type_checker tc(env);
    expr t = tc.check_ignore_undefined_universes(e).first;
    p.regular_stream() << e << " : " << t << "\n";
}

static environment app_builder_cmd(parser & p) {
    environment const & env = p.env();
    auto pos = p.pos();
    app_builder b(env);
    name c = p.check_constant_next("invalid #app_builder command, constant expected");
    bool has_mask = false;
    buffer<bool> mask;
    if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        has_mask = true;
        while (true) {
            name flag = p.check_constant_next("invalid #app_builder command, constant (true, false) expected");
            mask.push_back(flag == get_true_name());
            if (!p.curr_is_token(get_comma_tk()))
                break;
            p.next();
        }
        p.check_token_next(get_rbracket_tk(), "invalid #app_builder command, ']' expected");
    }

    buffer<expr> args;
    while (true) {
        expr e; level_param_names ls;
        std::tie(e, ls) = parse_local_expr(p);
        args.push_back(e);
        if (!p.curr_is_token(get_comma_tk()))
            break;
        p.next();
    }

    if (has_mask && args.size() > mask.size())
        throw parser_error(sstream() << "invalid #app_builder command, too many arguments", pos);

    optional<expr> r;
    if (has_mask)
        r = b.mk_app(c, mask.size(), mask.data(), args.data());
    else
        r = b.mk_app(c, args.size(), args.data());

    if (r) {
        check_expr_and_print(p, *r);
    } else {
        throw parser_error(sstream() << "failed to build application for '" << c << "'", pos);
    }

    return env;
}

static environment refl_cmd(parser & p) {
    environment const & env = p.env();
    auto pos = p.pos();
    app_builder b(env);
    name relname = p.check_constant_next("invalid #refl command, constant expected");
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    try {
        expr r = b.mk_refl(relname, e);
        check_expr_and_print(p, r);
    } catch (app_builder_exception &) {
        throw parser_error(sstream() << "failed to build refl proof", pos);
    }
    return env;
}

static environment symm_cmd(parser & p) {
    environment const & env = p.env();
    auto pos = p.pos();
    app_builder b(env);
    name relname = p.check_constant_next("invalid #symm command, constant expected");
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    try {
        expr r = b.mk_symm(relname, e);
        check_expr_and_print(p, r);
    } catch (app_builder_exception &) {
        throw parser_error(sstream() << "failed to build symm proof", pos);
    }
    return env;
}

static environment trans_cmd(parser & p) {
    environment const & env = p.env();
    auto pos = p.pos();
    app_builder b(env);
    name relname = p.check_constant_next("invalid #trans command, constant expected");
    expr H1, H2; level_param_names ls;
    std::tie(H1, ls) = parse_local_expr(p);
    p.check_token_next(get_comma_tk(), "invalid #trans command, ',' expected");
    std::tie(H2, ls) = parse_local_expr(p);
    try {
        expr r = b.mk_trans(relname, H1, H2);
        check_expr_and_print(p, r);
    } catch (app_builder_exception &) {
        throw parser_error(sstream() << "failed to build trans proof", pos);
    }
    return env;
}

enum class congr_kind { Simp, Default, Rel };

static environment congr_cmd_core(parser & p, congr_kind kind) {
    environment const & env = p.env();
    auto pos = p.pos();
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    tmp_type_context    ctx(env, p.get_options());
    app_builder         b(ctx);
    fun_info_manager    infom(ctx);
    congr_lemma_manager cm(b, infom);
    optional<congr_lemma> r;
    switch (kind) {
    case congr_kind::Simp:    r = cm.mk_congr_simp(e); break;
    case congr_kind::Default: r = cm.mk_congr(e); break;
    case congr_kind::Rel:     r = cm.mk_rel_iff_congr(e); break;
    }
    if (!r)
        throw parser_error("failed to generated congruence lemma", pos);
    auto out = p.regular_stream();
    out << "[";
    bool first = true;
    for (auto k : r->get_arg_kinds()) {
        if (!first) out << ", "; else first = false;
        switch (k) {
        case congr_arg_kind::Fixed:        out << "fixed"; break;
        case congr_arg_kind::FixedNoParam: out << "fixed-noparm"; break;
        case congr_arg_kind::Eq:           out << "eq";    break;
        case congr_arg_kind::HEq:          out << "heq";    break;
        case congr_arg_kind::Cast:         out << "cast";  break;
        }
    }
    out << "]\n";
    out << r->get_proof() << "\n:\n" << r->get_type() << "\n";;
    type_checker tc(env);
    expr type = tc.check(r->get_proof(), ls).first;
    if (!tc.is_def_eq(type, r->get_type()).first)
        throw parser_error("congruence lemma reported type does not match given type", pos);
    return env;
}

static environment congr_simp_cmd(parser & p) {
    return congr_cmd_core(p, congr_kind::Simp);
}

static environment congr_cmd(parser & p) {
    return congr_cmd_core(p, congr_kind::Default);
}

static environment congr_rel_cmd(parser & p) {
    return congr_cmd_core(p, congr_kind::Rel);
}

static environment hcongr_cmd(parser & p) {
    environment const & env = p.env();
    auto pos = p.pos();
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    tmp_type_context    ctx(env, p.get_options());
    app_builder         b(ctx);
    fun_info_manager    infom(ctx);
    congr_lemma_manager cm(b, infom);
    optional<congr_lemma> r = cm.mk_hcongr(e);
    if (!r)
        throw parser_error("failed to generated heterogeneous congruence lemma", pos);
    auto out = p.regular_stream();
    out << r->get_proof() << "\n:\n" << r->get_type() << "\n";;
    type_checker tc(env);
    expr type = tc.check(r->get_proof(), ls).first;
    if (!tc.is_def_eq(type, r->get_type()).first)
        throw parser_error("heterogeneous congruence lemma reported type does not match given type", pos);
    return env;
}

static environment simplify_cmd(parser & p) {
    name rel = p.check_constant_next("invalid #simplify command, constant expected");
    name ns = p.check_id_next("invalid #simplify command, id expected");
    unsigned o = p.parse_small_nat();

    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);

    blast::scope_debug scope(p.env(), p.ios());
    blast::simp_lemmas srss;
    if (ns == name("null")) {
    } else if (ns == name("env")) {
        srss = blast::get_simp_lemmas();
    } else {
        srss = blast::get_simp_lemmas(ns);
    }

    blast::simp::result r = blast::simplify(rel, e, srss);

    flycheck_information info(p.regular_stream());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.regular_stream() << "simplify result:\n";
    }

    if (!r.has_proof()) {
        p.regular_stream() << "(refl): " << r.get_new() << endl;
    } else {
        auto tc = mk_type_checker(p.env());

        expr pf_type = tc->check(r.get_proof(), ls).first;

        if (o == 0) p.regular_stream() << r.get_new() << endl;
        else if (o == 1) p.regular_stream() << r.get_proof() << endl;
        else p.regular_stream() << pf_type << endl;
    }

    return p.env();
}

static environment normalizer_cmd(parser & p) {
    environment const & env = p.env();
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    blast::scope_debug scope(p.env(), p.ios());
    expr r = blast::normalize(e);
    p.regular_stream() << r << endl;
    return env;
}

static environment unify_cmd(parser & p) {
    environment const & env = p.env();
    expr e1; level_param_names ls1;
    std::tie(e1, ls1) = parse_local_expr(p);
    p.check_token_next(get_comma_tk(), "invalid #unify command, proper usage \"#unify e1, e2\"");
    expr e2; level_param_names ls2;
    std::tie(e2, ls2) = parse_local_expr(p);
    default_type_context ctx(env, p.get_options());
    bool success = ctx.is_def_eq(e1, e2);
    flycheck_information info(p.regular_stream());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
    }
    p.regular_stream() << (success ? "success" : "fail") << endl;
    return env;
}

static environment abstract_expr_cmd(parser & p) {
    unsigned o = p.parse_small_nat();
    default_type_context ctx(p.env(), p.get_options());
    app_builder builder(p.env(), p.get_options());
    fun_info_manager fun_info(ctx);
    congr_lemma_manager congr_lemma(builder, fun_info);
    abstract_expr_manager ae_manager(congr_lemma);

    flycheck_information info(p.regular_stream());
    if (info.enabled()) p.display_information_pos(p.cmd_pos());

    expr e, a, b;
    level_param_names ls, ls1, ls2;
    if (o == 0) {
        // hash
        if (info.enabled()) p.regular_stream() << "abstract hash: " << endl;
        std::tie(e, ls) = parse_local_expr(p);
        p.regular_stream() << ae_manager.hash(e) << endl;
    } else {
        // is_equal
        if (info.enabled()) p.regular_stream() << "abstract is_equal: " << endl;
        std::tie(a, ls1) = parse_local_expr(p);
        p.check_token_next(get_comma_tk(), "invalid #abstract_expr command, ',' expected");
        std::tie(b, ls2) = parse_local_expr(p);
        p.regular_stream() << ae_manager.is_equal(a, b) << endl;
    }
    return p.env();
}

void init_cmd_table(cmd_table & r) {
    add_cmd(r, cmd_info("open",              "create aliases for declarations, and use objects defined in other namespaces",
                        open_cmd));
    add_cmd(r, cmd_info("export",            "create abbreviations for declarations, "
                        "and export objects defined in other namespaces", export_cmd));
    add_cmd(r, cmd_info("override",          "override notation declarations using the ones defined in the given namespace",
                        override_cmd));
    add_cmd(r, cmd_info("set_option",        "set configuration option", set_option_cmd));
    add_cmd(r, cmd_info("exit",              "exit", exit_cmd));
    add_cmd(r, cmd_info("print",             "print a string", print_cmd));
    add_cmd(r, cmd_info("section",           "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace",         "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",               "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("check",             "type check given expression, and display its type", check_cmd));
    add_cmd(r, cmd_info("eval",              "evaluate given expression", eval_cmd));
    add_cmd(r, cmd_info("find_decl",         "find definitions and/or theorems", find_cmd));
    add_cmd(r, cmd_info("local",             "define local attributes or notation", local_cmd));
    add_cmd(r, cmd_info("help",              "brief description of available commands and options", help_cmd));
    add_cmd(r, cmd_info("init_quotient",     "initialize quotient type computational rules", init_quotient_cmd));
    add_cmd(r, cmd_info("init_hits",         "initialize builtin HITs", init_hits_cmd));
    add_cmd(r, cmd_info("#erase_cache",      "erase cached definition (for debugging purposes)", erase_cache_cmd));
    add_cmd(r, cmd_info("#projections",      "generate projections for inductive datatype (for debugging purposes)", projections_cmd));
    add_cmd(r, cmd_info("#telescope_eq",     "(for debugging purposes)", telescope_eq_cmd));
    add_cmd(r, cmd_info("#app_builder",      "(for debugging purposes)", app_builder_cmd));
    add_cmd(r, cmd_info("#refl",             "(for debugging purposes)", refl_cmd));
    add_cmd(r, cmd_info("#trans",            "(for debugging purposes)", trans_cmd));
    add_cmd(r, cmd_info("#symm",             "(for debugging purposes)", symm_cmd));
    add_cmd(r, cmd_info("#compile",          "(for debugging purposes)", compile_cmd));
    add_cmd(r, cmd_info("#congr",            "(for debugging purposes)", congr_cmd));
    add_cmd(r, cmd_info("#hcongr",           "(for debugging purposes)", hcongr_cmd));
    add_cmd(r, cmd_info("#congr_simp",       "(for debugging purposes)", congr_simp_cmd));
    add_cmd(r, cmd_info("#congr_rel",        "(for debugging purposes)", congr_rel_cmd));
    add_cmd(r, cmd_info("#normalizer",       "(for debugging purposes)", normalizer_cmd));
    add_cmd(r, cmd_info("#unify",            "(for debugging purposes)", unify_cmd));
    add_cmd(r, cmd_info("#accessible",       "(for debugging purposes) display number of accessible declarations for blast tactic", accessible_cmd));
    add_cmd(r, cmd_info("#simplify",         "(for debugging purposes) simplify given expression", simplify_cmd));
    add_cmd(r, cmd_info("#abstract_expr",    "(for debugging purposes) call abstract expr methods", abstract_expr_cmd));

    register_decl_cmds(r);
    register_inductive_cmd(r);
    register_structure_cmd(r);
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
