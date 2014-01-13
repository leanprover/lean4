/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "kernel/expr.h"
#include "kernel/context.h"
#include "library/tactic/proof_state.h"
#include "frontends/lean/parser_types.h"

namespace lean {
/** \brief Exception used to track parsing erros, it does not leak outside of this class. */
struct parser_error : public exception {
    pos_info m_pos;
    parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
    parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
    virtual exception * clone() const { return new parser_error(m_msg.c_str(), m_pos); }
    virtual void rethrow() const { throw *this; }
};

/** \brief Exception used to report error in the tactic frontend available in the Lean parser. */
struct tactic_cmd_error : public parser_error {
    proof_state m_state;
    tactic_cmd_error(char const * msg, pos_info const & p, proof_state const & s):parser_error(msg, p), m_state(s) {}
    tactic_cmd_error(sstream const & msg, pos_info const & p, proof_state const & s):parser_error(msg, p), m_state(s) {}
    virtual exception * clone() const { return new tactic_cmd_error(m_msg.c_str(), m_pos, m_state); }
    virtual void rethrow() const { throw *this; }
};
}
