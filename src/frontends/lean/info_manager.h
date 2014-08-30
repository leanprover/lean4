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
class info_manager {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    info_manager();
    ~info_manager();

    void add_type_info(unsigned l, unsigned c, expr const & e);
    void add_synth_info(unsigned l, unsigned c, expr const & e);
    void add_overload_info(unsigned l, unsigned c, expr const & e);
    void add_coercion_info(unsigned l, unsigned c, expr const & e);
    void add_symbol_info(unsigned l, unsigned c, name const & n);
    void add_identifier_info(unsigned l, unsigned c, name const & full_id);
    void instantiate(substitution const & s);
    void merge(info_manager const & m, bool overwrite);
    void insert_line(unsigned l);
    void remove_line(unsigned l);
    void invalidate_line(unsigned l);
    void invalidate_line_col(unsigned l, unsigned c);
    void commit_upto(unsigned l, bool valid);
    void set_processed_upto(unsigned l);
    bool is_invalidated(unsigned l) const;
    void save_environment_options(unsigned l, environment const & env, options const & o);
    optional<pair<environment, options>> get_final_env_opts() const;
    void clear();
    void display(environment const & env, io_state const & ios, unsigned line) const;
    void block_new_info(bool f);
};
}
