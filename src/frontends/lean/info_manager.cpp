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
#include "library/choice.h"
#include "library/scoped_ext.h"
#include "library/pp_options.h"
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

/*
class extra_type_info_data : public info_data_cell {
protected:
    expr m_expr;
    expr m_type;
public:
    extra_type_info_data() {}
    extra_type_info_data(unsigned c, expr const & e, expr const & t):info_data_cell(c), m_expr(e), m_type(t) {}

    virtual info_kind kind() const { return info_kind::ExtraType; }

    virtual void get_message(io_state_stream const & ios, unsigned line) const {
        ios << "-- EXTRA_TYPE|" << line << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "--" << endl;
        ios << m_type << endl;
        ios << "-- ACK" << endl;
    }
};

class synth_info_data : public type_info_data {
public:
    synth_info_data(unsigned c, expr const & e):type_info_data(c, e) {}

    virtual info_kind kind() const { return info_kind::Synth; }

    virtual void get_message(io_state_stream const & ios, unsigned line) const {
        ios << "-- SYNTH|" << line << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "-- ACK" << endl;
    }

    expr const & get_expr() const { return m_expr; }
};

class overload_info_data : public info_data_cell {
    expr m_choices;
public:
    overload_info_data(unsigned c, expr const & e):info_data_cell(c), m_choices(e) {}

    virtual info_kind kind() const { return info_kind::Overload; }

    virtual void get_message(io_state_stream const & ios, unsigned line) const {
        ios << "-- OVERLOAD|" << line << "|" << get_column() << "\n";
        options os = ios.get_options();
        os = os.update_if_undef(get_pp_full_names_name(), true);
        auto new_ios = ios.update_options(os);
        for (unsigned i = 0; i < get_num_choices(m_choices); i++) {
            if (i > 0)
                ios << "--\n";
            new_ios << get_choice(m_choices, i) << endl;
        }
        new_ios << "-- ACK" << endl;
    }
};

class overload_notation_info_data : public info_data_cell {
    list<expr> m_alts;
public:
    overload_notation_info_data(unsigned c, list<expr> const & as):info_data_cell(c), m_alts(as) {}

    virtual info_kind kind() const { return info_kind::Overload; }

    virtual void get_message(io_state_stream const & ios, unsigned line) const {
        ios << "-- OVERLOAD|" << line << "|" << get_column() << "\n";
        options os = ios.get_options();
        os = os.update_if_undef(get_pp_full_names_name(), true);
        os = os.update_if_undef(get_pp_notation_name(), false);
        auto new_ios = ios.update_options(os);
        bool first = true;
        for (expr const & e : m_alts) {
            if (first) first = false; else ios << "--\n";
            new_ios << e << endl;
        }
        new_ios << "-- ACK" << endl;
    }
};

class coercion_info_data : public info_data_cell {
    expr m_expr;
    expr m_type;
public:
    coercion_info_data(unsigned c, expr const & e, expr const & t):
        info_data_cell(c), m_expr(e), m_type(t) {}

    virtual info_kind kind() const { return info_kind::Coercion; }

    virtual void get_message(io_state_stream const & ios, unsigned line) const {
        ios << "-- COERCION|" << line << "|" << get_column() << "\n";
        options os = ios.get_options();
        os = os.update_if_undef(get_pp_coercions_name(), true);
        ios.update_options(os) << m_expr << endl << "--" << endl << m_type << endl;
        ios << "-- ACK" << endl;
    }
};

class symbol_info_data : public info_data_cell {
    name m_symbol;
public:
    symbol_info_data(unsigned c, name const & s):info_data_cell(c), m_symbol(s) {}

    virtual info_kind kind() const { return info_kind::Symbol; }

    virtual void get_message(io_state_stream const & ios, unsigned line) const {
        ios << "-- SYMBOL|" << line << "|" << get_column() << "\n";
        ios << m_symbol << "\n";
        ios << "-- ACK" << endl;
    }
};
*/

info_data mk_type_info(expr const & e) { return info_data(new type_info_data(e)); }
info_data mk_identifier_info(name const & full_id) { return info_data(new identifier_info_data(full_id)); }
info_data mk_tactic_state_info(tactic_state const & s) { return info_data(new tactic_state_info_data(s)); }

/*info_data mk_extra_type_info(unsigned c, expr const & e, expr const & t) { return info_data(new extra_type_info_data(c, e, t)); }
info_data mk_synth_info(unsigned c, expr const & e) { return info_data(new synth_info_data(c, e)); }
info_data mk_overload_info(unsigned c, expr const & e) { return info_data(new overload_info_data(c, e)); }
info_data mk_overload_notation_info(unsigned c, list<expr> const & a) { return info_data(new overload_notation_info_data(c, a)); }
info_data mk_coercion_info(unsigned c, expr const & e, expr const & t) { return info_data(new coercion_info_data(c, e, t)); }
info_data mk_symbol_info(unsigned c, name const & s) { return info_data(new symbol_info_data(c, s)); }
*/

/*static bool is_tactic_type(expr const & e) {
    expr const * it = &e;
    while (is_pi(*it)) {
        it = &binding_body(*it);
    }
    return *it == get_tactic_type() || *it == get_tactic_expr_type() || *it == get_tactic_expr_list_type();
}*/

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

/*
void info_manager::add_extra_type_info(unsigned l, unsigned c, expr const & e, expr const & t) {
    //if (is_tactic_type(t))
    //    return;
    add_info(l, mk_extra_type_info(c, e, t));
}

void info_manager::add_synth_info(unsigned l, unsigned c, expr const & e) {
    add_info(l, mk_synth_info(c, e));
}

void info_manager::add_overload_info(unsigned l, unsigned c, expr const & e) {
    add_info(l, mk_overload_info(c, e));
}

void info_manager::add_overload_notation_info(unsigned l, unsigned c, list<expr> const & a) {
    add_info(l, mk_overload_notation_info(c, a));
}

void info_manager::add_coercion_info(unsigned l, unsigned c, expr const & e, expr const & t) {
    add_info(l, mk_coercion_info(c, e, t));
}

void info_manager::add_symbol_info(unsigned l, unsigned c, name const & s) {
    add_info(l, mk_symbol_info(c, s));
}

static bool is_tactic_id(name const & id) {
    if (id.is_atomic())
        return id == get_tactic_name();
    else
        return is_tactic_id(id.get_prefix());
}
*/

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
