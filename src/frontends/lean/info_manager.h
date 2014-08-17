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
    void merge(info_manager const & m);
    void insert_line(unsigned l);
    void remove_line(unsigned l);
    void invalidate_line(unsigned l);
    void commit_upto(unsigned l, bool valid);
    bool is_available(unsigned l) const;
    bool is_invalidated(unsigned l) const;
    void clear();
    void display(io_state_stream const & ios, unsigned line);
};
}
