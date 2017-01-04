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
#include "library/choice.h"
#include "library/scoped_ext.h"
#include "library/pp_options.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_format.h"
#include "library/compiler/vm_compiler.h"
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

#ifdef LEAN_SERVER
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

#ifdef LEAN_SERVER
    virtual void report(io_state_stream const & ios, json & record) const override {
        record["full-id"] = m_full_id.to_string();
        if (auto olean = get_decl_olean(ios.get_environment(), m_full_id))
            record["source"]["file"] = *olean;
        if (auto pos = get_decl_pos_info(ios.get_environment(), m_full_id)) {
            record["source"]["line"] = pos->first;
            record["source"]["column"] = pos->second;
        }
    }
#endif
};

#ifdef LEAN_SERVER
void tactic_state_info_data::report(io_state_stream const &, json & record) const {
    std::ostringstream ss;
    ss << m_state.pp();
    record["state"] = ss.str();
}

void smt_tactic_state_info_data::report(io_state_stream const &, json & record) const {
    std::ostringstream ss;
    vm_obj vm_smt_state = to_vm_list(m_smt_state, [](smt_goal const & g) { return to_obj(g); });
    ss << smt_state_pp(vm_smt_state, m_state);
    record["state"] = ss.str();
}
#endif

info_data mk_type_info(expr const & e) { return info_data(new type_info_data(e)); }
info_data mk_identifier_info(name const & full_id) { return info_data(new identifier_info_data(full_id)); }
info_data mk_tactic_state_info(tactic_state const & s) { return info_data(new tactic_state_info_data(s)); }
info_data mk_smt_tactic_state_info(list<smt_goal> const & ss, tactic_state const & ts) { return info_data(new smt_tactic_state_info_data(ss, ts)); }

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

void info_manager::add_tactic_state_info(unsigned l, unsigned c, tactic_state const & s) {
    add_info(l, c, mk_tactic_state_info(s));
}

void info_manager::add_smt_tactic_state_info(unsigned l, unsigned c, list<smt_goal> const & ss, tactic_state const & ts) {
    add_info(l, c, mk_smt_tactic_state_info(ss, ts));
}

#ifdef LEAN_SERVER
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
}
