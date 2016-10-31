/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "kernel/expr.h"
#include "library/io_state_stream.h"

namespace lean {
class proof_state;
class info_manager {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    info_manager();
    ~info_manager();

    void add_type_info(unsigned l, unsigned c, expr const & e);
    void add_extra_type_info(unsigned l, unsigned c, expr const & e, expr const & t);
    void add_synth_info(unsigned l, unsigned c, expr const & e);
    void add_overload_info(unsigned l, unsigned c, expr const & e);
    void add_overload_notation_info(unsigned l, unsigned c, list<expr> const & a);
    void add_coercion_info(unsigned l, unsigned c, expr const & e, expr const & t);
    void erase_coercion_info(unsigned l, unsigned c);
    void add_symbol_info(unsigned l, unsigned c, name const & n);
    void add_identifier_info(unsigned l, unsigned c, name const & full_id);
    void add_proof_state_info(unsigned l, unsigned c, tactic_state const & s);

    /** \brief Remove PROO_STATE info from [(start_line, start_line), (end_line, end_col)) */
    void remove_proof_state_info(unsigned start_line, unsigned start_col, unsigned end_line, unsigned end_col);

    optional<expr> get_type_at(unsigned line, unsigned col) const;
    optional<expr> get_meta_at(unsigned line, unsigned col) const;
    void display(environment const & env, options const & o, io_state const & ios, unsigned line,
                 optional<unsigned> const & col = optional<unsigned>()) const;
};
void initialize_info_manager();
void finalize_info_manager();
}
