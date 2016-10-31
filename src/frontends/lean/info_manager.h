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

class info_data;

enum class info_kind { Type = 0, ExtraType, Synth, Overload, Coercion, Symbol, Identifier, ProofState };

class info_data_cell {
    unsigned m_column;
MK_LEAN_RC();
    void dealloc() { delete this; }
protected:
    friend info_data;
public:
    info_data_cell():m_column(0), m_rc(0) {}
    info_data_cell(unsigned c):m_column(c), m_rc(0) {}
    virtual ~info_data_cell() {}
    /** \brief Return true iff the information is considered "cheap"
        If the column number is not provided in the method info_manager::display,
        then only "cheap" information is displayed.
    */
    virtual bool is_cheap() const { return true; }
    virtual info_kind kind() const = 0;
    unsigned get_column() const { return m_column; }
    virtual void display(io_state_stream const & ios, unsigned line) const = 0;
    virtual int compare(info_data_cell const & d) const;
};

class info_data {
private:
    info_data_cell * m_ptr;
public:
    //info_data();
    info_data(info_data_cell * c):m_ptr(c) { lean_assert(c); m_ptr->inc_ref(); }
    info_data(info_data const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    info_data(info_data && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~info_data() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(info_data & a, info_data & b) { std::swap(a.m_ptr, b.m_ptr); }
    info_data & operator=(info_data const & s) { LEAN_COPY_REF(s); }
    info_data & operator=(info_data && s) { LEAN_MOVE_REF(s); }
    int compare(info_data const & d) const { return m_ptr->compare(*d.m_ptr); }
    int compare(info_data_cell const & d) const { return m_ptr->compare(d); }
    unsigned get_column() const { return m_ptr->get_column(); }
    bool is_cheap() const { return m_ptr->is_cheap(); }
    void display(io_state_stream const & ios, unsigned line) const { m_ptr->display(ios, line); }
    info_data_cell const * raw() const { return m_ptr; }
    info_kind kind() const { return m_ptr->kind(); }
};

struct info_data_cmp {
    int operator()(info_data const & i1, info_data const & i2) const { return i1.compare(i2); }
};

typedef rb_tree<info_data, info_data_cmp> info_data_set;

class info_manager {
    rb_map<unsigned, info_data_set, std::less<unsigned>> m_line_data;

    void add_info(unsigned l, info_data data);
    info_data_set get_info_set(unsigned l) const;
public:
    void add_type_info(unsigned l, unsigned c, expr const & e);
    void add_extra_type_info(unsigned l, unsigned c, expr const & e, expr const & t);
    void add_synth_info(unsigned l, unsigned c, expr const & e);
    void add_overload_info(unsigned l, unsigned c, expr const & e);
    void add_overload_notation_info(unsigned l, unsigned c, list<expr> const & a);
    void add_coercion_info(unsigned l, unsigned c, expr const & e, expr const & t);
    void add_symbol_info(unsigned l, unsigned c, name const & n);
    void add_identifier_info(unsigned l, unsigned c, name const & full_id);
    void add_proof_state_info(unsigned l, unsigned c, tactic_state const & s);

    optional<expr> get_type_at(unsigned line, unsigned col) const;
    optional<expr> get_meta_at(unsigned line, unsigned col) const;
    void display(environment const & env, options const & o, io_state const & ios, unsigned line,
                 optional<unsigned> const & col = optional<unsigned>()) const;
};
}
