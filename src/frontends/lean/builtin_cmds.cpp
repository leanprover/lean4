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
#include "library/defeq_simp_lemmas.h"
#include "library/defeq_simplifier.h"
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
    options opts          = p.ios().get_options();
    opts                  = opts.update_if_undef(get_pp_metavar_args_name(), true);
    io_state new_ios(p.ios(), opts);
    auto out              = regular(p.env(), new_ios, tc->get_type_context());
    formatter fmt         = out.get_formatter();
    unsigned indent       = get_pp_indent(opts);
    format r = group(fmt(e) + space() + colon() + nest(indent, line() + fmt(type)));
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        out << "check result:\n";
    }
    out << mk_pair(r, opts) << endl;
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
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.ios().get_regular_stream() << "eval result:\n";
    }
    default_type_context tc(p.env(), p.get_options());
    auto out = regular(p.env(), p.ios(), tc);
    out << r << endl;
    return p.env();
}

environment exit_cmd(parser & p) {
    flycheck_warning wrn(p.ios());
    p.display_warning_pos(p.cmd_pos());
    p.ios().get_regular_stream() << " using 'exit' to interrupt Lean" << std::endl;
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
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.ios().get_regular_stream() << "help result:\n";
    }
    if (p.curr_is_token_or_id(get_options_tk())) {
        p.next();
        for (auto odecl : get_option_declarations()) {
            auto opt = odecl.second;
            p.ios().get_regular_stream()
                << "  " << opt.get_name() << " (" << opt.kind() << ") "
                << opt.get_description() << " (default: " << opt.get_default_value() << ")" << std::endl;
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
            p.ios().get_regular_stream()
                << "  " << n << ": " << cmds.find(n)->get_descr() << std::endl;
        };
    } else {
        p.ios().get_regular_stream()
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
    type_checker tc(p.env());
    auto out = regular(p.env(), p.ios(), tc.get_type_context());

    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        out << "simplify result:\n";
    }

    if (!r.has_proof()) {
        out << "(refl): " << r.get_new() << endl;
    } else {
        auto tc = mk_type_checker(p.env());

        expr pf_type = tc->check(r.get_proof(), ls).first;

        if (o == 0) out << r.get_new() << endl;
        else if (o == 1) out << r.get_proof() << endl;
        else out << pf_type << endl;
    }

    return p.env();
}

static environment normalizer_cmd(parser & p) {
    environment const & env = p.env();
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    blast::scope_debug scope(p.env(), p.ios());
    expr r = blast::normalize(e);
    type_checker tc(env);
    regular(env, p.ios(), tc.get_type_context()) << r << endl;
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
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
    }
    p.ios().get_regular_stream() << (success ? "success" : "fail") << std::endl;
    return env;
}

static environment defeq_simplify_cmd(parser & p) {
    auto pos = p.pos();
    environment const & env = p.env();
    name ns = p.check_id_next("invalid #simplify command, namespace or 'env' expected");

    defeq_simp_lemmas sls;
    if (ns == name("null")) {
    } else if (ns == name("env")) {
        sls = get_defeq_simp_lemmas(env);
    } else {
        sls = get_defeq_simp_lemmas(env, ns);
    }

    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);

    auto tc = mk_type_checker(p.env());
    default_tmp_type_context_pool pool(p.env(), p.get_options());
    expr e_simp = defeq_simplify(pool, p.get_options(), sls, e);
    if (!tc->is_def_eq(e, e_simp).first) {
        throw parser_error("defeq_simplify result not definitionally equal to input expression", pos);
    }
    flycheck_information info(p.ios());
    auto out = regular(p.env(), p.ios(), tc->get_type_context());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        out << "defeq_simplify result:\n";
    }

    out << e_simp << endl;
    return env;
}

static environment abstract_expr_cmd(parser & p) {
    unsigned o = p.parse_small_nat();
    default_type_context ctx(p.env(), p.get_options());
    app_builder builder(p.env(), p.get_options());
    fun_info_manager fun_info(ctx);
    congr_lemma_manager congr_lemma(builder, fun_info);
    abstract_expr_manager ae_manager(congr_lemma);

    std::ostream & out = p.ios().get_regular_stream();
    flycheck_information info(p.ios());
    if (info.enabled()) p.display_information_pos(p.cmd_pos());
    expr e, a, b;
    level_param_names ls, ls1, ls2;
    if (o == 0) {
        // hash
        if (info.enabled()) out << "abstract hash: " << std::endl;
        std::tie(e, ls) = parse_local_expr(p);
        out << ae_manager.hash(e) << std::endl;
    } else {
        // is_equal
        if (info.enabled()) out << "abstract is_equal: " << std::endl;
        std::tie(a, ls1) = parse_local_expr(p);
        p.check_token_next(get_comma_tk(), "invalid #abstract_expr command, ',' expected");
        std::tie(b, ls2) = parse_local_expr(p);
        out << ae_manager.is_equal(a, b) << std::endl;
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
    add_cmd(r, cmd_info("#normalizer",       "(for debugging purposes)", normalizer_cmd));
    add_cmd(r, cmd_info("#unify",            "(for debugging purposes)", unify_cmd));
    add_cmd(r, cmd_info("#simplify",         "(for debugging purposes) simplify given expression", simplify_cmd));
    add_cmd(r, cmd_info("#defeq_simplify",   "(for debugging purposes) defeq-simplify given expression", defeq_simplify_cmd));
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
