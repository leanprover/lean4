/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/utf8.h"
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "library/class.h"
#include "library/deep_copy.h"
#include "frontends/lean/parser_state.h"
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
    case expr_kind::Local: case expr_kind::Var:
        return save_pos(copy(e), p);
    case expr_kind::App:
        return save_pos(::lean::mk_app(copy_with_new_pos(app_fn(e), p),
                                       copy_with_new_pos(app_arg(e), p)),
                        p);
    case expr_kind::Lambda: case expr_kind::Pi:
        return save_pos(update_binding(e,
                                       copy_with_new_pos(binding_domain(e), p),
                                       copy_with_new_pos(binding_body(e), p)),
                        p);
    case expr_kind::Let:
        return save_pos(::lean::mk_let(let_name(e),
                                       copy_with_new_pos(let_type(e), p),
                                       copy_with_new_pos(let_value(e), p),
                                       copy_with_new_pos(let_body(e), p)),
                        p);
    case expr_kind::Macro: {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(copy_with_new_pos(macro_arg(e, i), p));
        return save_pos(::lean::mk_macro(macro_def(e), args.size(), args.data()), p);
    }}
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

}
