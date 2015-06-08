/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "kernel/expr.h"
#include "kernel/metavar.h"
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
    void add_proof_state_info(unsigned l, unsigned c, proof_state const & e);

    /** \brief Remove PROO_STATE info from [(start_line, start_line), (end_line, end_col)) */
    void remove_proof_state_info(unsigned start_line, unsigned start_col, unsigned end_line, unsigned end_col);

    void instantiate(substitution const & s);

    void merge(info_manager const & m, bool overwrite);
    void insert_line(unsigned l);
    void remove_line(unsigned l);
    void invalidate_line(unsigned l);
    void invalidate_line_col(unsigned l, unsigned c);
    void commit_upto(unsigned l, bool valid);
    void set_processed_upto(unsigned l);
    bool is_invalidated(unsigned l) const;
    void save_environment_options(unsigned l, unsigned col, environment const & env, options const & o);
    optional<pair<environment, options>> get_final_env_opts() const;
    optional<pair<environment, options>> get_closest_env_opts(unsigned linenum) const;
    optional<expr> get_type_at(unsigned line, unsigned col) const;
    optional<expr> get_meta_at(unsigned line, unsigned col) const;
    void clear();
    void display(environment const & env, io_state const & ios, unsigned line,
                 optional<unsigned> const & col = optional<unsigned>()) const;
    /** \brief Block new information from being inserted into this info_manager.
        \remark #start_iteration unblocks it.
    */
    void block_new_info();
    /** \brief Mark the start of a new information collection cycle.
        It also enables new information to be added, i.e., it will undo
        the effect of #block_new_info.
    */
    void start_from(unsigned l);
    unsigned get_processed_upto() const;
};
void initialize_info_manager();
void finalize_info_manager();
}
