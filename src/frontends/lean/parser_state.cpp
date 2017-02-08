/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/utf8.h"
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/error_msgs.h"
#include "library/class.h"
#include "library/explicit.h"
#include "library/deep_copy.h"
#include "library/quote.h"
#include "library/aliases.h"
#include "frontends/lean/parser_state.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

namespace lean {
parser_state::parser_state(environment const & env, io_state const & ios, header_ptr const & h,
                           bool use_exceptions, std::shared_ptr<snapshot const> const & s) {
    m_header               = h;
    m_context              = std::make_shared<context>(env, ios);

    m_tv_curr_idx          = 0;
    m_tv_cmd_idx           = 0;
    m_next_inst_idx        = 1;
    m_next_tag_idx         = 0;
    m_ignore_noncomputable = false;

    m_use_exceptions       = use_exceptions;
    m_has_params           = false;
    m_in_quote             = false;
    m_in_pattern           = false;
    m_found_errors         = false;
    m_used_sorry           = false;
    m_ignore_noncomputable = false;
    m_id_behavior          = static_cast<unsigned>(id_behavior::ErrorIfUndef);
    m_complete             = false;

    if (s) {
        m_context->m_env                = s->m_env;
        m_context->m_ios.set_options(s->m_options);
        m_context->m_local_level_decls  = s->m_lds;
        m_context->m_local_decls        = s->m_eds;
        m_context->m_level_variables    = s->m_lvars;
        m_context->m_variables          = s->m_vars;
        m_context->m_include_vars       = s->m_include_vars;
        m_context->m_scope_stack        = s->m_parser_scope_stack;
        m_ignore_noncomputable          = s->m_noncomputable_theory;
        m_next_inst_idx                 = s->m_next_inst_idx;
    }
}

void parser_state::ensure_exclusive_context() {
    if (m_context.unique()) return;
    m_context = std::make_shared<context>(*m_context);
}

token const * parser_state::lookahead(int delta) const {
    int idx = static_cast<int>(m_tv_cmd_idx) + delta;
    if (idx >= 0 && idx < static_cast<int>(get_token_vector().size()))
        return &get_token_vector()[idx];
    else
        return nullptr;
}

void parser_state::check_break_at_pos(break_at_pos_exception::token_context ctxt) {
    auto p = pos();
    if (m_break_at_pos && p.first == m_break_at_pos->first && p.second <= m_break_at_pos->second) {
        name tk;
        if (curr_is_identifier()) {
            tk = get_name_val();
        } else if (curr_is_command() || curr_is_keyword()) {
            tk = get_token_info().token();
            // When completing at the end of a token that cannot be extended into an identifier,
            // start an empty completion instead (in the next call to `check_break_before/at_pos`, using the correct
            // context).
            if (m_complete && m_break_at_pos->second == p.second + tk.utf8_size() - 1 &&
                    !curr_is_token(get_period_tk())) {
                auto s = tk.to_string();
                if (!is_id_rest(get_utf8_last_char(s.c_str()), s.c_str() + s.size()))
                    return;
            }
        } else {
            return;
        }
        if (m_break_at_pos->second < p.second + tk.utf8_size())
            throw break_at_pos_exception(p, tk, ctxt);
    }
}

void parser_state::check_break_before(break_at_pos_exception::token_context ctxt) {
    if (m_break_at_pos && *m_break_at_pos < pos())
        throw break_at_pos_exception(*m_break_at_pos, "", ctxt);
}

tag parser_state::get_tag(expr e) {
    tag t = e.get_tag();
    if (t == nulltag) {
        t = m_next_tag_idx;
        e.set_tag(t);
        m_next_tag_idx++;
    }
    return t;
}

name parser_state::mk_anonymous_inst_name() {
    name n = ::lean::mk_anonymous_inst_name(m_next_inst_idx);
    m_next_inst_idx++;
    return n;
}

optional<pos_info> parser_state::get_pos_info(expr const & e) const {
    tag t = e.get_tag();
    if (t == nulltag)
        return optional<pos_info>();
    if (auto it = m_pos_table.find(t))
        return optional<pos_info>(*it);
    else
        return optional<pos_info>();
}

token const * parser_state::get_last_cmd_tk() const {
    unsigned i = m_tv_cmd_idx;
    while (true) {
        token const & tk = get_token(i);
        if (tk.kind() == token_kind::CommandKeyword &&
            tk.get_token_info().token() != get_end_tk()) {
            return &tk;
        }
        if (i == 0) return nullptr;
        i--;
    }
}

pos_info parser_state::get_some_pos() const {
    if (token const * tk = get_last_cmd_tk())
        return tk->get_pos();
    else
        return get_token(0).get_pos();
}

expr parser_state::save_pos(expr e, pos_info p) {
    auto t = get_tag(e);
    if (!m_pos_table.contains(t))
        m_pos_table.insert(t, p);
    return e;
}

expr parser_state::update_pos(expr e, pos_info p) {
    auto t = get_tag(e);
    m_pos_table.insert(t, p);
    return e;
}

expr parser_state::rec_save_pos(expr const & e, pos_info p) {
    unsigned m = std::numeric_limits<unsigned>::max();
    pos_info dummy(m, 0);
    for_each(e, [&](expr const & e, unsigned) {
            if (pos_of(e, dummy).first == m) {
                save_pos(e, p);
                return true;
            }  else {
                return false;
            }
        });
    return e;
}

/** \brief Create a copy of \c e, and the position of new expression with p */
expr parser_state::copy_with_new_pos(expr const & e, pos_info p) {
    switch (e.kind()) {
    case expr_kind::Sort: case expr_kind::Constant: case expr_kind::Meta:
    case expr_kind::Var:  case expr_kind::Local:
        return save_pos(copy(e), p);
    case expr_kind::App:
        return save_pos(::lean::mk_app(copy_with_new_pos(app_fn(e), p),
                                       copy_with_new_pos(app_arg(e), p)),
                        p);
    case expr_kind::Lambda:
        return save_pos(::lean::mk_lambda(binding_name(e),
                                          copy_with_new_pos(binding_domain(e), p),
                                          copy_with_new_pos(binding_body(e), p),
                                          binding_info(e)),

                        p);
    case expr_kind::Pi:
        return save_pos(::lean::mk_pi(binding_name(e),
                                      copy_with_new_pos(binding_domain(e), p),
                                      copy_with_new_pos(binding_body(e), p),
                                      binding_info(e)),
                        p);
    case expr_kind::Let:
        return save_pos(::lean::mk_let(let_name(e),
                                       copy_with_new_pos(let_type(e), p),
                                       copy_with_new_pos(let_value(e), p),
                                       copy_with_new_pos(let_body(e), p)),
                        p);
    case expr_kind::Macro:
        if (is_quote(e)) {
            return save_pos(mk_quote_core(copy_with_new_pos(get_quote_expr(e), p)), p);
        } else {
            buffer<expr> args;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                args.push_back(copy_with_new_pos(macro_arg(e, i), p));
            return save_pos(::lean::mk_macro(macro_def(e), args.size(), args.data()), p);
        }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

pos_info parser_state::pos_of(expr const & e, pos_info default_pos) const {
    tag t = e.get_tag();
    if (t == nulltag)
        return default_pos;
    if (auto it = m_pos_table.find(t))
        return *it;
    else
        return default_pos;
}

bool parser_state::curr_is_token(name const & tk) const {
    return
        (curr() == token_kind::Keyword || curr() == token_kind::CommandKeyword) &&
        get_token_info().value() == tk;
}

bool parser_state::curr_is_token_or_id(name const & tk) const {
    if (curr() == token_kind::Keyword || curr() == token_kind::CommandKeyword)
        return get_token_info().value() == tk;
    else if (curr() == token_kind::Identifier)
        return get_name_val() == tk;
    else
        return false;
}

void parser_state::check_token_next(name const & tk, char const * msg) {
    if (!curr_is_token(tk))
        throw parser_error(msg, pos());
    next();
}

void parser_state::check_token_or_id_next(name const & tk, char const * msg) {
    if (!curr_is_token_or_id(tk))
        throw parser_error(msg, pos());
    next();
}

name parser_state::check_id_next(char const * msg, break_at_pos_exception::token_context ctxt) {
    // initiate empty completion even if following token is not an identifier
    check_break_before(ctxt);
    if (!curr_is_identifier())
        throw parser_error(msg, pos());
    name r = get_name_val();
    try {
        next();
    } catch (break_at_pos_exception & e) {
        e.m_token_info.m_context = ctxt;
        throw;
    }
    return r;
}

static void check_not_internal(name const & id, pos_info const & p) {
    if (is_internal_name(id))
        throw parser_error(sstream() << "invalid declaration name '" << id << "', identifiers starting with '_' are reserved to the system", p);
}

name parser_state::check_decl_id_next(char const * msg, break_at_pos_exception::token_context ctxt) {
    auto p  = pos();
    name id = check_id_next(msg, ctxt);
    check_not_internal(id, p);
    return id;
}

name parser_state::check_atomic_id_next(char const * msg) {
    auto p  = pos();
    name id = check_id_next(msg);
    if (!id.is_atomic())
        throw parser_error(msg, p);
    return id;
}

name parser_state::check_atomic_decl_id_next(char const * msg) {
    auto p  = pos();
    name id = check_atomic_id_next(msg);
    check_not_internal(id, p);
    return id;
}

expr parser_state::mk_app(expr fn, expr arg, pos_info const & p) {
    return save_pos(::lean::mk_app(fn, arg), p);
}

expr parser_state::mk_app(expr fn, buffer<expr> const & args, pos_info const & p) {
    expr r = fn;
    for (expr const & arg : args) {
        r = mk_app(r, arg, p);
    }
    return r;
}

expr parser_state::mk_app(std::initializer_list<expr> const & args, pos_info const & p) {
    lean_assert(args.size() >= 2);
    auto it = args.begin();
    expr r = *it;
    it++;
    for (; it != args.end(); it++)
        r = mk_app(r, *it, p);
    return r;
}

parser_state::scope parser_state::mk_scope(optional<options> const & opts) {
    return scope(opts, m_context->m_level_variables, m_context->m_variables, m_context->m_include_vars,
                 m_next_inst_idx, m_has_params, m_context->m_local_level_decls, m_context->m_local_decls);
}

void parser_state::restore_scope(scope const & s) {
    ensure_exclusive_context();
    if (s.m_options) {
        m_context->m_ios.set_options(*s.m_options);
    }
    m_context->m_local_level_decls  = s.m_local_level_decls;
    m_context->m_local_decls        = s.m_local_decls;
    m_context->m_level_variables    = s.m_level_variables;
    m_context->m_variables          = s.m_variables;
    m_context->m_include_vars       = s.m_include_vars;
    m_has_params                    = s.m_has_params;
    m_next_inst_idx                 = s.m_next_inst_idx;
}

void parser_state::push_local_scope(bool save_options) {
    ensure_exclusive_context();
    optional<options> opts;
    if (save_options)
        opts = m_context->m_ios.get_options();
    m_context->m_scope_stack = cons(mk_scope(opts), m_context->m_scope_stack);
}

void parser_state::pop_local_scope() {
    lean_assert(m_context->m_scope_stack);
    ensure_exclusive_context();
    auto s = head(m_context->m_scope_stack);
    restore_scope(s);
    m_context->m_scope_stack = tail(m_context->m_scope_stack);
}

void parser_state::clear_expr_locals() {
    ensure_exclusive_context();
    m_context->m_local_decls = local_expr_decls();
}

void parser_state::add_local_level(name const & n, level const & l, bool is_variable) {
    ensure_exclusive_context();
    if (env().is_universe(n))
        throw exception(sstream() << "invalid universe declaration, '" << n << "' shadows a global universe");
    if (m_context->m_local_level_decls.contains(n))
        throw exception(sstream() << "invalid universe declaration, '" << n << "' shadows a local universe");
    m_context->m_local_level_decls.insert(n, l);
    if (is_variable) {
        lean_assert(is_param(l));
        m_context->m_level_variables.insert(n);
    }
}

void parser_state::add_local_expr(name const & n, expr const & p, bool is_variable) {
    ensure_exclusive_context();
    m_context->m_local_decls.insert(n, p);
    if (is_variable) {
        lean_assert(is_local(p));
        m_context->m_variables.insert(local_pp_name(p));
    }
}

environment parser_state::add_local_ref(environment const & env, name const & n, expr const & ref) {
    add_local_expr(n, ref, false);
    if (is_as_atomic(ref)) {
        buffer<expr> args;
        expr f = get_app_args(get_as_atomic_arg(ref), args);
        if (is_explicit(f))
            f = get_explicit_arg(f);
        if (is_constant(f)) {
            return ::lean::add_local_ref(env, const_name(f), ref);
        } else {
            return env;
        }
    } else if (is_constant(ref) && const_levels(ref)) {
        return ::lean::add_local_ref(env, const_name(ref), ref);
    } else {
        return env;
    }
}

static void check_no_metavars(name const & n, expr const & e) {
    lean_assert(is_local(e));
    if (has_metavar(e)) {
        throw generic_exception(none_expr(), [=](formatter const & fmt) {
                format r("failed to add declaration '");
                r += format(n);
                r += format("' to local context, type has metavariables");
                r += pp_until_meta_visible(fmt, mlocal_type(e));
                return r;
            });
    }
}

void parser_state::add_variable(name const & n, expr const & v) {
    lean_assert(is_local(v));
    check_no_metavars(n, v);
    add_local_expr(n, v, true);
}

void parser_state::add_parameter(name const & n, expr const & p) {
    lean_assert(is_local(p));
    check_no_metavars(n, p);
    add_local_expr(n, p, false);
    m_has_params = true;
}

bool parser_state::update_local_binder_info(name const & n, binder_info const & bi) {
    auto it = get_local(n);
    if (!it || !is_local(*it)) return false;

    buffer<pair<name, expr>> entries;
    to_buffer(m_context->m_local_decls.get_entries(), entries);
    std::reverse(entries.begin(), entries.end());
    unsigned idx = m_context->m_local_decls.find_idx(n);
    lean_assert(idx > 0);
    lean_assert_eq(entries[idx-1].second, *it);

    buffer<expr> old_locals;
    buffer<expr> new_locals;
    old_locals.push_back(*it);
    expr new_l = update_local(*it, bi);
    entries[idx-1].second = new_l;
    new_locals.push_back(new_l);

    for (unsigned i = idx; i < entries.size(); i++) {
        expr const & curr_e = entries[i].second;
        expr r = is_local(curr_e) ? mlocal_type(curr_e) : curr_e;
        if (std::any_of(old_locals.begin(), old_locals.end(), [&](expr const & l) { return depends_on(r, l); })) {
            r  = replace_locals(r, old_locals, new_locals);
            if (is_local(curr_e)) {
                expr new_e = update_mlocal(curr_e, r);
                entries[i].second = new_e;
                old_locals.push_back(curr_e);
                new_locals.push_back(new_e);
            } else {
                entries[i].second = r;
            }
        }
    }
    auto new_entries = m_context->m_local_decls.get_entries();
    unsigned sz_to_updt = entries.size() - idx + 1;
    for (unsigned i = 0; i < sz_to_updt; i++)
        new_entries = tail(new_entries); // remove entries that will be updated
    for (unsigned i = idx-1; i < entries.size(); i++)
        new_entries = cons(entries[i], new_entries);
    ensure_exclusive_context();
    m_context->m_local_decls.update_entries(new_entries);
    return true;
}

unsigned parser_state::get_local_index(name const & n) const {
    return m_context->m_local_decls.find_idx(n);
}

void parser_state::get_include_variables(buffer<expr> & vars) const {
    m_context->m_include_vars.for_each([&](name const & n) {
            vars.push_back(*get_local(n));
        });
}

list<expr> parser_state::locals_to_context() const {
    return map_filter<expr>(m_context->m_local_decls.get_entries(),
                            [](pair<name, expr> const & p, expr & out) {
                                out = p.second;
                                return is_local(p.second);
                            });
}
}
