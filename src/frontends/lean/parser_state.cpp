/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/parser_state.h"

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
}
