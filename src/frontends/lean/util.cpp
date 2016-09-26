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
#include "library/constants.h"
#include "library/typed_expr.h"
#include "library/placeholder.h"
#include "library/unfold_macros.h"
#include "library/choice.h"
#include "library/string.h"
#include "library/num.h"
#include "library/util.h"
#include "library/normalize.h"
#include "library/metavar_context.h"
#include "library/replace_visitor.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/decl_util.h" // TODO(Leo): remove
namespace lean {
void consume_until_end(parser & p) {
    while (!p.curr_is_token(get_end_tk())) {
        if (p.curr() == scanner::token_kind::Eof)
            return;
        p.next();
    }
    p.next();
}

void check_command_period_or_eof(parser const & p) {
    if (!p.curr_is_command() && !p.curr_is_eof() && !p.curr_is_token(get_period_tk()))
        throw parser_error("unexpected token, '.', command, or end-of-file expected", p.pos());
}

void check_command_period_open_binder_or_eof(parser const & p) {
    if (!p.curr_is_command() && !p.curr_is_eof() && !p.curr_is_token(get_period_tk()) &&
        !p.curr_is_token(get_lparen_tk()) && !p.curr_is_token(get_lbracket_tk()) &&
        !p.curr_is_token(get_lcurly_tk()) && !p.curr_is_token(get_ldcurly_tk()))
        throw parser_error("unexpected token, '(', '{', '[', '⦃', '.', command, or end-of-file expected", p.pos());
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

bool is_eqn_prefix(parser & p, bool bar_only = false) {
    return p.curr_is_token(get_bar_tk()) || (!bar_only && p.curr_is_token(get_comma_tk()));
}

// Return the local levels in \c ls that are not associated with variables
levels collect_local_nonvar_levels(parser & p, level_param_names const & ls) {
    buffer<level> section_ls_buffer;
    for (name const & l : ls) {
        if (p.is_local_level(l) && !p.is_local_level_variable(l))
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
            // if (is_by(e))
            // return false; // do not visit children
            if (is_local(e))
                ls.insert(e);
            return true;
        });
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

// TODO(Leo): delete these headers
void collect_annonymous_inst_implicit(parser const & p, collected_locals & locals);
void sort_locals(buffer<expr> const & locals, parser const & p, buffer<expr> & ps);

list<expr> locals_to_context(expr const & e, parser const & p) {
    collected_locals ls;
    collect_locals_ignoring_tactics(e, ls);
    collect_annonymous_inst_implicit(p, ls);
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

std::tuple<expr, level_param_names> parse_local_expr(parser & p, metavar_context & mctx, bool relaxed) {
    expr e = p.parse_expr();
    bool check_unassigend = !relaxed;
    expr new_e; level_param_names ls;
    std::tie(new_e, ls) = p.elaborate(mctx, e, check_unassigend);
    level_param_names new_ls = to_level_param_names(collect_univ_params(new_e));
    return std::make_tuple(new_e, new_ls);
}

std::tuple<expr, level_param_names> parse_local_expr(parser & p, bool relaxed) {
    metavar_context mctx;
    return parse_local_expr(p, mctx, relaxed);
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

environment open_prec_aliases(environment const & env) {
    name prec("std", "prec");
    return overwrite_aliases(env, prec, name());
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

pair<name, option_kind> parse_option_name(parser & p, char const * error_msg) {
    auto id_pos  = p.pos();
    name id = p.check_id_next(error_msg);
    option_declarations decls = get_option_declarations();
    auto it = decls.find(id);
    if (!it) {
        // add "lean" prefix
        name lean_id = name("lean") + id;
        it = decls.find(lean_id);
        if (!it) {
            throw parser_error(sstream() << "unknown option '" << id
                               << "', type 'help options.' for list of available options", id_pos);
        } else {
            id = lean_id;
        }
    }
    return mk_pair(id, it->kind());
}

expr mk_tactic_unit() {
    return mk_app(mk_constant(get_tactic_name()), mk_constant(get_unit_name()));
}

expr quote_name(name const & n) {
    if (n.is_anonymous()) {
        return mk_constant(get_name_anonymous_name());
    } else if (n.is_string()) {
        expr prefix = quote_name(n.get_prefix());
        expr str    = from_string(n.get_string());
        return mk_app(mk_constant(get_name_mk_string_name()), str, prefix);
    } else {
        lean_unreachable();
    }
}
}
