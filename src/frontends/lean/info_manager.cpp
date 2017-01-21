/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include <set>
#include <string>
#include "util/lean_path.h"
#include "kernel/type_checker.h"
#include "library/trace.h"
#include "library/documentation.h"
#include "library/scoped_ext.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/json.h"
#include "frontends/lean/info_manager.h"

namespace lean {
class type_info_data : public info_data_cell {
protected:
    expr m_expr;
public:
    type_info_data(expr const & e): m_expr(e) {}

    expr const & get_type() const { return m_expr; }

    virtual void instantiate_mvars(metavar_context const & mctx) override {
        m_expr = metavar_context(mctx).instantiate_mvars(m_expr);
    }

#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const override {
        std::ostringstream ss;
        ss << flatten(ios.get_formatter()(m_expr));
        record["type"] = ss.str();
    }
#endif
};

class identifier_info_data : public info_data_cell {
    name m_full_id;
public:
    identifier_info_data(name const & full_id): m_full_id(full_id) {}

#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const override {
        record["full-id"] = m_full_id.to_string();
        add_source_info(ios.get_environment(), m_full_id, record);
        if (auto doc = get_doc_string(ios.get_environment(), m_full_id))
            record["doc"] = *doc;
    }
#endif
};

#ifdef LEAN_JSON
void vm_obj_format_info::report(io_state_stream const & ios, json & record) const {
    if (!m_cache) {
        vm_state S(m_env, ios.get_options());
        vm_obj thunk = m_thunk.to_vm_obj();
        const_cast<vm_obj_format_info*>(this)->m_cache = to_format(S.invoke(thunk, mk_vm_unit()));
    }
    std::ostringstream ss;
    ss << mk_pair(*m_cache, ios.get_options());
    record["state"] = ss.str();
}
#endif

info_data mk_type_info(expr const & e) { return info_data(new type_info_data(e)); }
info_data mk_identifier_info(name const & full_id) { return info_data(new identifier_info_data(full_id)); }
info_data mk_vm_obj_format_info(environment const & env, vm_obj const & thunk) { return info_data(new vm_obj_format_info(env, thunk)); }

void info_manager::add_info(unsigned l, unsigned c, info_data data) {
    line_info_data_set line_set = m_line_data[l];
    line_set.insert(c, cons<info_data>(data, line_set[c]));
    m_line_data.insert(l, line_set);
}

line_info_data_set info_manager::get_line_info_set(unsigned l) const {
    if (auto it = m_line_data.find(l))
        return *it;
    return {};
}

void info_manager::instantiate_mvars(metavar_context const & mctx) {
    m_line_data.for_each([&](unsigned, line_info_data_set const & set) {
            set.for_each([&](unsigned, list<info_data> const & data) {
                    for (info_data const & info : data)
                        info.instantiate_mvars(mctx);
                });
        });
}

void info_manager::merge(info_manager const & info) {
    info.m_line_data.for_each([&](unsigned line, line_info_data_set const & set) {
            set.for_each([&](unsigned col, list<info_data> const & data) {
                    buffer<info_data> b;
                    to_buffer(data, b);
                    unsigned i = b.size();
                    while (i > 0) {
                        --i;
                        add_info(line, col, b[i]);
                    }
                });
        });
}

void info_manager::add_type_info(unsigned l, unsigned c, expr const & e) {
    add_info(l, c, mk_type_info(e));
}

void info_manager::add_identifier_info(unsigned l, unsigned c, name const & full_id) {
    add_info(l, c, mk_identifier_info(full_id));
}

void info_manager::add_vm_obj_format_info(unsigned l, unsigned c, environment const & env, vm_obj const & thunk) {
    add_info(l, c, mk_vm_obj_format_info(env, thunk));
}

#ifdef LEAN_JSON
void info_manager::get_info_record(environment const & env, options const & o, io_state const & ios, unsigned line,
                                   unsigned col, json & record, std::function<bool (info_data const &)> pred) const {
    type_context tc(env, o);
    io_state_stream out = regular(env, ios, tc).update_options(o);
    get_line_info_set(line).for_each([&](unsigned c, list<info_data> const & ds) {
        if (c == col) {
            for (auto const & d : ds) {
                if (!pred || pred(d))
                    d.report(out, record);
            }
        }
    });
}
#endif

LEAN_THREAD_PTR(info_manager, g_info_m);
scoped_info_manager::scoped_info_manager(info_manager *infom) {
    m_old = g_info_m;
    g_info_m = infom;
}
scoped_info_manager::~scoped_info_manager() {
    g_info_m = m_old;
}
info_manager * get_global_info_manager() {
    return g_info_m;
}

vm_obj tactic_save_info_thunk(vm_obj const & line, vm_obj const & col, vm_obj const & thunk, vm_obj const & s) {
    try {
        if (g_info_m) {
            g_info_m->add_vm_obj_format_info(force_to_unsigned(line), force_to_unsigned(col), to_tactic_state(s).env(), thunk);
        }
        return mk_tactic_success(to_tactic_state(s));
    } catch (exception & ex) {
        return mk_tactic_exception(ex, to_tactic_state(s));
    }
}

void initialize_info_manager() {
    DECLARE_VM_BUILTIN(name({"tactic", "save_info_thunk"}),  tactic_save_info_thunk);
}
void finalize_info_manager() {
}
}
