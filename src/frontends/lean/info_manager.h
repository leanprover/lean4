/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "util/thread.h"
#include "kernel/expr.h"
#include "kernel/metavar.h"
#include "library/io_state_stream.h"

namespace lean {
class info_data;
class info_data_cell {
    unsigned m_line;
    unsigned m_column;
    MK_LEAN_RC();
    void dealloc();
protected:
    friend info_data;
    virtual info_data_cell * instantiate(substitution &) const;
public:
    info_data_cell():m_line(0), m_column(0), m_rc(0) {}
    info_data_cell(unsigned l, unsigned c):m_line(l), m_column(c) {}
    virtual ~info_data_cell() {}
    unsigned get_line() const { return m_line; }
    unsigned get_column() const { return m_column; }
    virtual int compare(info_data_cell const & d) const;
    virtual void display(io_state_stream const & ios) const = 0;
};

class info_data {
private:
    info_data_cell * m_ptr;
public:
    info_data();
    info_data(info_data_cell * c):m_ptr(c) { lean_assert(c); m_ptr->inc_ref(); }
    info_data(info_data const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    info_data(info_data && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~info_data() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(info_data & a, info_data & b) { std::swap(a.m_ptr, b.m_ptr); }
    info_data & operator=(info_data const & s) { LEAN_COPY_REF(s); }
    info_data & operator=(info_data && s) { LEAN_MOVE_REF(s); }
    void display(io_state_stream const & ios) const { m_ptr->display(ios); }
    int compare(info_data const & d) const { return m_ptr->compare(*d.m_ptr); }
    int compare(info_data_cell const & d) const { return m_ptr->compare(d); }
    info_data instantiate(substitution & s) const;
    unsigned get_line() const { return m_ptr->get_line(); }
    unsigned get_column() const { return m_ptr->get_column(); }
};
bool operator==(info_data const & i1, info_data const & i2);

info_data mk_type_info(unsigned l, unsigned c, expr const & e);
info_data mk_synth_info(unsigned l, unsigned c, expr const & e);
info_data mk_overload_info(unsigned l, unsigned c, expr const & e);
info_data mk_coercion_info(unsigned l, unsigned c, expr const & e);

class info_manager {
    typedef std::vector<info_data> data_vector;
    mutex       m_mutex;

    unsigned    m_sorted_upto;
    data_vector m_data;
    void add_core(info_data const & d);
    unsigned find(unsigned line, unsigned column);
    void sort_core();
public:
    info_manager();
    void invalidate(unsigned sline);
    void add(info_data const & d);
    void append(std::vector<info_data> & v, bool remove_duplicates = true);
    void sort();
    void display(io_state_stream const & ios, unsigned line);
};
}
