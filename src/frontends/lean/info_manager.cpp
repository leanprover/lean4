/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include <set>
#include <library/tactic/tactic_state.h>
#include <frontends/lean/json.h>
#include "library/choice.h"
#include "library/scoped_ext.h"
#include "library/pp_options.h"
#include "info_manager.h"

namespace lean {
class type_info_data : public info_data_cell {
protected:
    expr m_expr;
public:
    type_info_data(expr const & e): m_expr(e) {}

    expr const & get_type() const { return m_expr; }

    virtual void add_info(io_state_stream const & ios, json & record) const {
        std::ostringstream ss;
        ss << flatten(ios.get_formatter()(m_expr));
        record["type"] = ss.str();
    }
};

class identifier_info_data : public info_data_cell {
    name m_full_id;
public:
    identifier_info_data(name const & full_id): m_full_id(full_id) {}

    virtual void add_info(io_state_stream const &, json & record) const {
        record["full-id"] = m_full_id.to_string();
    }
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

class proof_state_info_data : public info_data_cell {
    tactic_state m_state;
public:
    proof_state_info_data(unsigned c, tactic_state const & s):info_data_cell(c), m_state(s) {}
    virtual info_kind kind() const { return info_kind::ProofState; }
    virtual void add_info(io_state_stream const & ios, unsigned line) const {
        ios << "-- PROOF_STATE|" << line << "|" << get_column() << "\n";
        bool first = true;
        for (expr const & g : m_state.goals()) {
            if (first)
                first = false;
            else
                ios << "--" << endl;
            ios << m_state.pp_goal(g) << endl;
        }
        ios << "-- ACK" << endl;
    }
};
*/

info_data mk_type_info(expr const & e) { return info_data(new type_info_data(e)); }
info_data mk_identifier_info(name const & full_id) { return info_data(new identifier_info_data(full_id)); }
/*info_data mk_extra_type_info(unsigned c, expr const & e, expr const & t) { return info_data(new extra_type_info_data(c, e, t)); }
info_data mk_synth_info(unsigned c, expr const & e) { return info_data(new synth_info_data(c, e)); }
info_data mk_overload_info(unsigned c, expr const & e) { return info_data(new overload_info_data(c, e)); }
info_data mk_overload_notation_info(unsigned c, list<expr> const & a) { return info_data(new overload_notation_info_data(c, a)); }
info_data mk_coercion_info(unsigned c, expr const & e, expr const & t) { return info_data(new coercion_info_data(c, e, t)); }
info_data mk_symbol_info(unsigned c, name const & s) { return info_data(new symbol_info_data(c, s)); }
info_data mk_proof_state_info(unsigned c, tactic_state const & s) { return info_data(new proof_state_info_data(c, s)); }
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

void info_manager::add_type_info(unsigned l, unsigned c, expr const & e) {
    //if (is_tactic_type(e))
    //    return;
    add_info(l, c, mk_type_info(e));
}

void info_manager::add_identifier_info(unsigned l, unsigned c, name const & full_id) {
    //if (is_tactic_id(full_id))
    //    return;
    add_info(l, c, mk_identifier_info(full_id));
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

void info_manager::add_proof_state_info(unsigned l, unsigned c, tactic_state const & s) {
    add_info(l, mk_proof_state_info(c, s));
}
*/

json info_manager::get_info_record(environment const & env, options const & o, io_state const & ios, unsigned line,
                                   unsigned col) const {
    json record;
    get_line_info_set(line).for_each([&](unsigned c, list<info_data> const & ds) {
        if (c == col) {
            for (auto const & d : ds) {
                type_context tc(env, o);
                io_state_stream out = regular(env, ios, tc).update_options(o);
                d.add_info(out, record);
            }
        }
    });
    return record;
}
}
