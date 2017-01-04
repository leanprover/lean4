/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <vector>
#include <string>
#include "kernel/expr.h"
#include "library/io_state_stream.h"
#include "library/metavar_context.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/smt_state.h"
#include "frontends/lean/json.h"

namespace lean {

class proof_state;

class info_data;

class info_data_cell {
    MK_LEAN_RC();
    void dealloc() { delete this; }
protected:
    friend info_data;
public:
    info_data_cell():m_rc(0) {}
    virtual ~info_data_cell() {}
    virtual void instantiate_mvars(metavar_context const &) {}
#ifdef LEAN_SERVER
    virtual void report(io_state_stream const & ios, json & record) const = 0;
#endif
};

class tactic_state_info_data : public info_data_cell {
protected:
    tactic_state m_state;
public:
    tactic_state_info_data(tactic_state const & s):m_state(s) {}

#ifdef LEAN_SERVER
    virtual void report(io_state_stream const &, json & record) const override;
#endif
};

class smt_tactic_state_info_data : public tactic_state_info_data {
    list<smt_goal> m_smt_state;
public:
    smt_tactic_state_info_data(list<smt_goal> const & ss, tactic_state const & ts):
        tactic_state_info_data(ts), m_smt_state(ss) {}

#ifdef LEAN_SERVER
    virtual void report(io_state_stream const &, json & record) const override;
#endif
};

class info_data {
private:
    info_data_cell * m_ptr;
public:
    info_data(info_data_cell * c):m_ptr(c) { lean_assert(c); m_ptr->inc_ref(); }
    info_data(info_data const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    info_data(info_data && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~info_data() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(info_data & a, info_data & b) { std::swap(a.m_ptr, b.m_ptr); }
    info_data & operator=(info_data const & s) { LEAN_COPY_REF(s); }
    info_data & operator=(info_data && s) { LEAN_MOVE_REF(s); }
    info_data_cell const * raw() const { return m_ptr; }
#ifdef LEAN_SERVER
    void report(io_state_stream const & ios, json & record) const {
        return m_ptr->report(ios, record);
    }
#endif
    void instantiate_mvars(metavar_context const & mctx) const {
        m_ptr->instantiate_mvars(mctx);
    }
};

typedef rb_map<unsigned, list<info_data>, unsigned_cmp> line_info_data_set;

class info_manager {
    std::string m_file_name;
    rb_map<unsigned, line_info_data_set, unsigned_cmp> m_line_data;

    void add_info(unsigned l, unsigned c, info_data data);
    line_info_data_set get_line_info_set(unsigned l) const;
public:
    info_manager() {}
    info_manager(std::string const & file_name) : m_file_name(file_name) {}

    std::string get_file_name() const { return m_file_name; }

    bool empty() const { return m_line_data.empty(); }

    void add_type_info(unsigned l, unsigned c, expr const & e);
    void add_identifier_info(unsigned l, unsigned c, name const & full_id);
    void add_tactic_state_info(unsigned l, unsigned c, tactic_state const & s);
    void add_smt_tactic_state_info(unsigned l, unsigned c, list<smt_goal> const & ss, tactic_state const & ts);
    void instantiate_mvars(metavar_context const & mctx);
    void merge(info_manager const & info);

#ifdef LEAN_SERVER
    void get_info_record(environment const & env, options const & o, io_state const & ios, unsigned line,
                         unsigned col, json & record, std::function<bool (info_data const &)> pred = {}) const;
#endif
};

info_manager * get_global_info_manager();
class scoped_info_manager {
    info_manager * m_old;
public:
    scoped_info_manager(info_manager * infom);
    ~scoped_info_manager();
};

class auto_reporting_info_manager_scope {
    optional<info_manager> m_infom;
    scoped_info_manager m_infom_scope;

public:
    auto_reporting_info_manager_scope(std::string const & file_name, bool enabled) :
            m_infom(enabled ? optional<info_manager>(info_manager(file_name)) : optional<info_manager>()),
            m_infom_scope(enabled ? &*m_infom : nullptr) {}

    ~auto_reporting_info_manager_scope() {
        if (m_infom && !m_infom->empty()) {
            try {
                report_info_manager(*m_infom);
            } catch (...) {}
        }
    }
};
}
