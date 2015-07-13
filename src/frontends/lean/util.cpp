/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/error_msgs.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "library/aliases.h"
#include "library/normalize.h"
#include "library/placeholder.h"
#include "library/abbreviation.h"
#include "library/unfold_macros.h"
#include "library/choice.h"
#include "library/num.h"
#include "library/replace_visitor.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"

namespace lean {
void consume_until_end(parser & p) {
    while (!p.curr_is_token(get_end_tk())) {
        if (p.curr() == scanner::token_kind::Eof)
            return;
        p.next();
    }
    p.next();
}

bool parse_persistent(parser & p, bool & persistent) {
    if (p.curr_is_token_or_id(get_persistent_tk())) {
        p.next();
        persistent = true;
        return true;
    } else {
        return false;
    }
}

void check_command_period_or_eof(parser const & p) {
    if (!p.curr_is_command() && !p.curr_is_eof() && !p.curr_is_token(get_period_tk()) &&
        !p.curr_is_script_block())
        throw parser_error("unexpected token, '.', command, Lua script, or end-of-file expected", p.pos());
}

void check_command_period_open_binder_or_eof(parser const & p) {
    if (!p.curr_is_command() && !p.curr_is_eof() && !p.curr_is_token(get_period_tk()) &&
        !p.curr_is_script_block() &&
        !p.curr_is_token(get_lparen_tk()) && !p.curr_is_token(get_lbracket_tk()) &&
        !p.curr_is_token(get_lcurly_tk()) && !p.curr_is_token(get_ldcurly_tk()))
        throw parser_error("unexpected token, '(', '{', '[', '⦃', '.', command, Lua script, or end-of-file expected", p.pos());
}

void check_atomic(name const & n) {
    if (!n.is_atomic())
        throw exception(sstream() << "invalid declaration name '" << n << "', identifier must be atomic");
}

void check_in_section(parser const & p) {
    if (!in_section(p.env()))
        throw exception(sstream() << "invalid command, it must be used in a section");
}

bool is_root_namespace(name const & n) {
    return n == get_root_tk();
}

name remove_root_prefix(name const & n) {
    return n.replace_prefix(get_root_tk(), name());
}

// Sort local names by order of occurrence, and copy the associated parameters to ps
void sort_locals(buffer<expr> const & locals, parser const & p, buffer<expr> & ps) {
    for (expr const & l : locals) {
        // we only copy the locals that are in p's local context
        if (p.is_local_decl(l))
            ps.push_back(l);
    }
    std::sort(ps.begin(), ps.end(), [&](expr const & p1, expr const & p2) {
            bool is_var1 = p.is_local_variable(p1);
            bool is_var2 = p.is_local_variable(p2);
            if (!is_var1 && is_var2)
                return true;
            else if (is_var1 && !is_var2)
                return false;
            else
                return p.get_local_index(p1) < p.get_local_index(p2);
        });
}

// Return the local levels in \c ls that are not associated with variables
levels collect_local_nonvar_levels(parser & p, level_param_names const & ls) {
    buffer<level> section_ls_buffer;
    for (name const & l : ls) {
        if (p.get_local_level_index(l) && !p.is_local_level_variable(l))
            section_ls_buffer.push_back(mk_param_univ(l));
        else
            break;
    }
    return to_list(section_ls_buffer.begin(), section_ls_buffer.end());
}

// Version of collect_locals(expr const & e, collected_locals & ls) that ignores local constants occurring in
// tactics.
static void collect_locals_ignoring_tactics(expr const & e, collected_locals & ls) {
    if (!has_local(e))
        return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_local(e))
                return false;
            if (is_by(e))
                return false; // do not visit children
            if (is_local(e))
                ls.insert(e);
            return true;
        });
}

// Collect local constants occurring in type and value, sort them, and store in ctx_ps
void collect_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & ctx_ps) {
    collected_locals ls;
    buffer<expr> include_vars;
    p.get_include_variables(include_vars);
    for (expr const & param : include_vars) {
        if (is_local(param)) {
            collect_locals_ignoring_tactics(mlocal_type(param), ls);
            ls.insert(param);
        }
    }
    collect_locals_ignoring_tactics(type, ls);
    collect_locals_ignoring_tactics(value, ls);
    sort_locals(ls.get_collected(), p, ctx_ps);
}

name_set collect_univ_params_ignoring_tactics(expr const & e, name_set const & ls) {
    if (!has_param_univ(e)) {
        return ls;
    } else {
        name_set r = ls;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_param_univ(e)) {
                    return false;
                } else if (is_by(e)) {
                    return false; // do not visit children
                } else if (is_sort(e)) {
                    collect_univ_params_core(sort_level(e), r);
                } else if (is_constant(e)) {
                    for (auto const & l : const_levels(e))
                        collect_univ_params_core(l, r);
                }
                return true;
            });
        return r;
    }
}

void remove_local_vars(parser const & p, buffer<expr> & locals) {
    unsigned j = 0;
    for (unsigned i = 0; i < locals.size(); i++) {
        expr const & param = locals[i];
        if (!is_local(param) || !p.is_local_variable(param)) {
            locals[j] = param;
            j++;
        }
    }
    locals.shrink(j);
}

levels remove_local_vars(parser const & p, levels const & ls) {
    return filter(ls, [&](level const & l) {
            return !is_param(l) || !p.is_local_level_variable(param_id(l));
        });
}

list<expr> locals_to_context(expr const & e, parser const & p) {
    collected_locals ls;
    collect_locals_ignoring_tactics(e, ls);
    buffer<expr> locals;
    sort_locals(ls.get_collected(), p, locals);
    std::reverse(locals.begin(), locals.end());
    return to_list(locals.begin(), locals.end());
}

expr mk_local_ref(name const & n, levels const & ctx_ls, unsigned num_ctx_params, expr const * ctx_params) {
    buffer<expr> params;
    for (unsigned i = 0; i < num_ctx_params; i++)
        params.push_back(mk_explicit(ctx_params[i]));
    return mk_as_atomic(mk_app(mk_explicit(mk_constant(n, ctx_ls)), params));
}

bool is_local_ref(expr const & e) {
    if (!is_as_atomic(e))
        return false;
    expr const & imp_arg = get_as_atomic_arg(e);
    if (!is_app(imp_arg))
        return false;
    buffer<expr> locals;
    expr const & f = get_app_args(imp_arg, locals);
    return
        is_explicit(f) &&
        is_constant(get_explicit_arg(f)) &&
        std::all_of(locals.begin(), locals.end(),
                    [](expr const & l) {
                        return is_explicit(l) && is_local(get_explicit_arg(l));
                    });
}

expr update_local_ref(expr const & e, name_set const & lvls_to_remove, name_set const & locals_to_remove) {
    lean_assert(is_local_ref(e));
    if (locals_to_remove.empty() && lvls_to_remove.empty())
        return e;
    buffer<expr> locals;
    expr const & f = get_app_args(get_as_atomic_arg(e), locals);
    lean_assert(is_explicit(f));

    expr new_f;
    if (!lvls_to_remove.empty()) {
        expr const & c = get_explicit_arg(f);
        lean_assert(is_constant(c));
        new_f = mk_explicit(update_constant(c, filter(const_levels(c), [&](level const & l) {
                        return is_placeholder(l) || (is_param(l) && !lvls_to_remove.contains(param_id(l)));
                    })));
    } else {
        new_f = f;
    }

    if (!locals_to_remove.empty()) {
        unsigned j = 0;
        for (unsigned i = 0; i < locals.size(); i++) {
            expr const & l = locals[i];
            if (!locals_to_remove.contains(mlocal_name(get_explicit_arg(l)))) {
                locals[j] = l;
                j++;
            }
        }
        locals.shrink(j);
    }

    if (locals.empty()) {
        return get_explicit_arg(new_f);
    } else {
        return mk_as_atomic(mk_app(new_f, locals));
    }
}

expr Fun(buffer<expr> const & locals, expr const & e, parser & p) {
    bool use_cache = false;
    return p.rec_save_pos(Fun(locals, e, use_cache), p.pos_of(e));
}

expr Pi(buffer<expr> const & locals, expr const & e, parser & p) {
    bool use_cache = false;
    return p.rec_save_pos(Pi(locals, e, use_cache), p.pos_of(e));
}

template<bool is_lambda>
static expr mk_binding_as_is(unsigned num, expr const * locals, expr const & b) {
    expr r     = abstract_locals(b, num, locals);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = abstract_locals(mlocal_type(l), i, locals);
        if (is_lambda)
            r = mk_lambda(local_pp_name(l), mk_as_is(t), r, local_info(l));
        else
            r = mk_pi(local_pp_name(l), mk_as_is(t), r, local_info(l));
    }
    return r;
}

expr Fun_as_is(buffer<expr> const & locals, expr const & e, parser & p) {
    return p.rec_save_pos(mk_binding_as_is<true>(locals.size(), locals.data(), e), p.pos_of(e));
}

expr Pi_as_is(buffer<expr> const & locals, expr const & e, parser & p) {
    return p.rec_save_pos(mk_binding_as_is<false>(locals.size(), locals.data(), e), p.pos_of(e));
}

level mk_result_level(environment const & env, buffer<level> const & r_lvls) {
    bool impredicative = env.impredicative();
    if (r_lvls.empty()) {
        return impredicative ? mk_level_one() : mk_level_zero();
    } else {
        level r = r_lvls[0];
        for (unsigned i = 1; i < r_lvls.size(); i++)
            r = mk_max(r, r_lvls[i]);
        r = normalize(r);
        if (is_not_zero(r))
            return normalize(r);
        else
            return impredicative ? normalize(mk_max(r, mk_level_one())) : normalize(r);
    }
}

bool occurs(level const & u, level const & l) {
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (l == u) { found = true; return false; }
            return true;
        });
    return found;
}

/** \brief Functional object for converting the universe metavariables in an expression in new universe parameters.
    The substitution is updated with the mapping metavar -> new param.
    The set of parameter names m_params and the buffer m_new_params are also updated.
*/
class univ_metavars_to_params_fn : public replace_visitor {
    environment const &        m_env;
    local_decls<level> const & m_lls;
    substitution &             m_subst;
    name_set &                 m_params;
    buffer<name> &             m_new_params;
    unsigned                   m_next_idx;

    /** \brief Create a new universe parameter s.t. the new name does not occur in \c m_params, nor it is
        a global universe in \e m_env or in the local_decls<level> m_lls.
        The new name is added to \c m_params, and the new level parameter is returned.
        The name is of the form "l_i" where \c i >= m_next_idx.
    */
    level mk_new_univ_param() {
        name l("l");
        name r = l.append_after(m_next_idx);
        while (m_lls.contains(r) || m_params.contains(r) || m_env.is_universe(r)) {
            m_next_idx++;
            r = l.append_after(m_next_idx);
        }
        m_params.insert(r);
        m_new_params.push_back(r);
        return mk_param_univ(r);
    }

public:
    univ_metavars_to_params_fn(environment const & env, local_decls<level> const & lls, substitution & s,
                               name_set & ps, buffer<name> & new_ps):
        m_env(env), m_lls(lls), m_subst(s), m_params(ps), m_new_params(new_ps), m_next_idx(1) {}

    level apply(level const & l) {
        return replace(l, [&](level const & l) {
                if (!has_meta(l))
                    return some_level(l);
                if (is_meta(l)) {
                    if (auto it = m_subst.get_level(meta_id(l))) {
                        return some_level(*it);
                    } else {
                        level new_p = mk_new_univ_param();
                        m_subst.assign(l, new_p);
                        return some_level(new_p);
                    }
                }
                return none_level();
            });
    }

    virtual expr visit_sort(expr const & e) {
        return update_sort(e, apply(sort_level(e)));
    }

    virtual expr visit_constant(expr const & e) {
        levels ls = map(const_levels(e), [&](level const & l) { return apply(l); });
        return update_constant(e, ls);
    }
};

expr univ_metavars_to_params(environment const & env, local_decls<level> const & lls, substitution & s,
                             name_set & ps, buffer<name> & new_ps, expr const & e) {
    return univ_metavars_to_params_fn(env, lls, s, ps, new_ps)(e);
}

std::tuple<expr, level_param_names> parse_local_expr(parser & p, bool relaxed) {
    expr e   = p.parse_expr();
    list<expr> ctx = p.locals_to_context();
    level_param_names new_ls;
    if (relaxed)
        std::tie(e, new_ls) = p.elaborate_relaxed(e, ctx);
    else
        std::tie(e, new_ls) = p.elaborate(e, ctx);
    level_param_names ls = to_level_param_names(collect_univ_params(e));
    return std::make_tuple(e, ls);
}

optional<name> is_uniquely_aliased(environment const & env, name const & n) {
    if (auto it = is_expr_aliased(env, n))
        if (length(get_expr_aliases(env, *it)) == 1)
            return it;
    return optional<name>();
}

name get_decl_short_name(name const & d, environment const & env) {
    // using namespace override resolution rule
    list<name> const & ns_list = get_namespaces(env);
    for (name const & ns : ns_list) {
        if (is_prefix_of(ns, d) && ns != d)
            return d.replace_prefix(ns, name());
    }
    // if the alias is unique use it
    if (auto it = is_uniquely_aliased(env, d))
        return *it;
    else
        return d;
}

environment open_num_notation(environment const & env) {
    name num("num");
    try {
        bool persistent     = false;
        environment new_env = override_notation(env, num, persistent);
        return overwrite_aliases(new_env, num, name());
    } catch (exception &) {
        // num namespace is not available, then use only the aliases
        return overwrite_aliases(env, num, name());
    }
}

environment open_prec_aliases(environment const & env) {
    name prec("std", "prec");
    return overwrite_aliases(env, prec, name());
}

name get_priority_namespace() {
    return name("std", "priority");
}

environment open_priority_aliases(environment const & env) {
    return overwrite_aliases(env, get_priority_namespace(), name());
}

char const * open_binder_string(binder_info const & bi, bool unicode) {
    if (bi.is_implicit()) return "{";
    else if (bi.is_inst_implicit()) return "[";
    else if (bi.is_strict_implicit() && unicode) return "⦃";
    else if (bi.is_strict_implicit() && !unicode) return "{{";
    else return "(";
}

char const * close_binder_string(binder_info const & bi, bool unicode) {
    if (bi.is_implicit()) return "}";
    else if (bi.is_inst_implicit()) return "]";
    else if (bi.is_strict_implicit() && unicode) return "⦄";
    else if (bi.is_strict_implicit() && !unicode) return "}}";
    else return ")";
}

expr postprocess(environment const & env, expr const & e) {
    return eta_reduce(expand_abbreviations(env, unfold_untrusted_macros(env, e)));
}


struct elim_choice_fn : public replace_visitor {
    name m_prio_ns;
    elim_choice_fn():m_prio_ns(get_priority_namespace()) {}

    virtual expr visit_macro(expr const & e) {
        if (is_choice(e)) {
            for (unsigned i = 0; i < get_num_choices(e); i++) {
                expr const & c = get_choice(e, i);
                if (is_constant(c) && const_name(c).get_prefix() == m_prio_ns)
                    return c;
            }
            throw exception("invalid priority expression, it contains overloaded symbols");
        } else {
            return replace_visitor::visit_macro(e);
        }
    }
};

optional<unsigned> parse_priority(parser & p) {
    if (p.curr_is_token(get_priority_tk())) {
        p.next();
        auto pos = p.pos();
        environment env = open_priority_aliases(open_num_notation(p.env()));
        parser::local_scope scope(p, env);
        expr val = p.parse_expr();
        val = elim_choice_fn()(val);
        val = normalize(p.env(), val);
        if (optional<mpz> mpz_val = to_num(val)) {
            if (!mpz_val->is_unsigned_int())
                throw parser_error("invalid 'priority', argument does not fit in a machine integer", pos);
            p.check_token_next(get_rbracket_tk(), "invalid 'priority', ']' expected");
            return optional<unsigned>(mpz_val->get_unsigned_int());
        } else {
            throw parser_error("invalid 'priority', argument does not evaluate to a numeral", pos);
        }
    } else {
        return optional<unsigned>();
    }
}

pair<name, option_kind> parse_option_name(parser & p, char const * error_msg) {
    auto id_pos  = p.pos();
    name id = p.check_id_next(error_msg);
    auto decl_it = get_option_declarations().find(id);
    if (decl_it == get_option_declarations().end()) {
        // add "lean" prefix
        name lean_id = name("lean") + id;
        decl_it = get_option_declarations().find(lean_id);
        if (decl_it == get_option_declarations().end()) {
            throw parser_error(sstream() << "unknown option '" << id
                               << "', type 'help options.' for list of available options", id_pos);
        } else {
            id = lean_id;
        }
    }
    return mk_pair(id, decl_it->second.kind());
}
}
