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
#include "library/vm/vm.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/json.h"

namespace lean {
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
#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const = 0;
#endif
};

class vm_obj_format_info : public info_data_cell {
    environment      m_env;
    ts_vm_obj        m_thunk;
    optional<format> m_cache;
public:
    vm_obj_format_info(environment const & env, vm_obj const & thunk):m_env(env), m_thunk(thunk) {}
#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const;
#endif
};

class hole_info_data : public info_data_cell {
    tactic_state m_state;
    expr         m_args;
    pos_info     m_begin_pos;
    pos_info     m_end_pos;
    /* TODO(Leo): we need to store the string for command containing the whole, and where it starts */
public:
    hole_info_data(tactic_state const & s, expr const & args, pos_info const & b, pos_info const & e):
        m_state(s), m_args(args), m_begin_pos(b), m_end_pos(e) {}

#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const override;
#endif
    tactic_state const & get_tactic_state() const { return m_state; }
    expr const & get_args() const { return m_args; }
    pos_info const & get_begin_pos() const { return m_begin_pos; }
    pos_info const & get_end_pos() const { return m_end_pos; }
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
#ifdef LEAN_JSON
    void report(io_state_stream const & ios, json & record) const {
        return m_ptr->report(ios, record);
    }
#endif
    void instantiate_mvars(metavar_context const & mctx) const {
        m_ptr->instantiate_mvars(mctx);
    }
};

hole_info_data const * is_hole_info_data(info_data const & d);
hole_info_data const & to_hole_info_data(info_data const & d);

typedef rb_map<unsigned, list<info_data>, unsigned_cmp> line_info_data_set;

class info_manager : public log_entry_cell {
    std::string m_file_name;
    rb_map<unsigned, line_info_data_set, unsigned_cmp> m_line_data;

    void add_info(pos_info pos, info_data data);
public:
    info_manager() {}
    info_manager(std::string const & file_name) : m_file_name(file_name) {}

    std::string get_file_name() const { return m_file_name; }

    bool empty() const { return m_line_data.empty(); }

    void add_type_info(pos_info pos, expr const & e);
    void add_identifier_info(pos_info pos, name const & full_id);
    /* Takes type info from global declaration with the given name. */
    void add_const_info(environment const & env, pos_info pos, name const & full_id);
    void add_vm_obj_format_info(pos_info pos, environment const & env, vm_obj const & thunk);
    void add_hole_info(pos_info const & begin_pos, pos_info const & end_pos, tactic_state const & s, expr const & hole_args);

    line_info_data_set get_line_info_set(unsigned l) const;
    rb_map<unsigned, line_info_data_set, unsigned_cmp> const & get_line_info_sets() const { return m_line_data; }

    void instantiate_mvars(metavar_context const & mctx);
    void merge(info_manager const & info);

#ifdef LEAN_JSON
    void get_info_record(environment const & env, options const & o, io_state const & ios, pos_info pos,
                         json & record, std::function<bool (info_data const &)> pred = {}) const;
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
    std::shared_ptr<info_manager> m_infom;
    scoped_info_manager m_infom_scope;

public:
    auto_reporting_info_manager_scope(std::string const & file_name, bool enabled) :
            m_infom(enabled ? std::make_shared<info_manager>(file_name) : nullptr),
            m_infom_scope(enabled ? &*m_infom : nullptr) {}

    ~auto_reporting_info_manager_scope() {
        if (m_infom && !m_infom->empty()) {
            try {
                logtree().add(m_infom);
            } catch (...) {}
        }
    }
};

void initialize_info_manager();
void finalize_info_manager();
}
