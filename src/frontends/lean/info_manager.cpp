/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "library/choice.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/pp_options.h"

namespace lean {
void info_data_cell::dealloc() { delete this; }

int info_data_cell::compare(info_data_cell const & d) const {
    if (m_line != d.m_line)
        return m_line < d.m_line ? -1 : 1;
    if (m_column != d.m_column)
        return m_column < d.m_column ? -1 : 1;
    if (typeid(*this) != typeid(d))
        return typeid(*this).before(typeid(d)) ? -1 : 1;
    return 0;
}

info_data_cell * info_data_cell::instantiate(substitution &) const { return nullptr; }

struct tmp_info_data : public info_data_cell {
    tmp_info_data(unsigned l, unsigned c):info_data_cell(l, c) {}
    virtual void display(io_state_stream const &) const { lean_unreachable(); } // LCOV_EXCL_LINE
};

static info_data g_dummy(new tmp_info_data(0, 0));

info_data::info_data():info_data(g_dummy) {}
info_data info_data::instantiate(substitution & s) const {
    if (auto r = m_ptr->instantiate(s)) {
        return info_data(r);
    } else {
        return *this;
    }
}

class type_info_data : public info_data_cell {
protected:
    expr m_expr;
public:
    type_info_data() {}
    type_info_data(unsigned l, unsigned c, expr const & e):info_data_cell(l, c), m_expr(e) {}

    expr const & get_type() const {
        return m_expr;
    }

    virtual void display(io_state_stream const & ios) const {
        ios << "-- TYPE|" << get_line() << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "-- ACK" << endl;
    }

    virtual info_data_cell * instantiate(substitution & s) const {
        expr e = s.instantiate(m_expr);
        if (is_eqp(e, m_expr))
            return nullptr;
        else
            return new type_info_data(get_line(), get_column(), e);
    }
};

class synth_info_data : public type_info_data {
public:
    synth_info_data(unsigned l, unsigned c, expr const & e):type_info_data(l, c, e) {}
    virtual void display(io_state_stream const & ios) const {
        ios << "-- SYNTH|" << get_line() << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "-- ACK" << endl;
    }
};

class overload_info_data : public info_data_cell {
    expr m_choices;
public:
    overload_info_data(unsigned l, unsigned c, expr const & e):info_data_cell(l, c), m_choices(e) {}
    virtual void display(io_state_stream const & ios) const {
        ios << "-- OVERLOAD|" << get_line() << "|" << get_column() << "\n";
        options os = ios.get_options();
        os = os.update(get_pp_full_names_option_name(), true);
        auto new_ios = ios.update_options(os);
        for (unsigned i = 0; i < get_num_choices(m_choices); i++) {
            if (i > 0)
                ios << "--\n";
            new_ios << get_choice(m_choices, i) << endl;
        }
        new_ios << "-- ACK" << endl;
    }
};

class coercion_info_data : public info_data_cell {
    expr m_coercion;
public:
    coercion_info_data(unsigned l, unsigned c, expr const & e):info_data_cell(l, c), m_coercion(e) {}
    virtual void display(io_state_stream const & ios) const {
        ios << "-- COERCION|" << get_line() << "|" << get_column() << "\n";
        options os = ios.get_options();
        os = os.update(get_pp_coercion_option_name(), true);
        ios.update_options(os) << m_coercion << endl;
        ios << "-- ACK" << endl;
    }
};

info_data mk_type_info(unsigned l, unsigned c, expr const & e) { return info_data(new type_info_data(l, c, e)); }
info_data mk_synth_info(unsigned l, unsigned c, expr const & e) { return info_data(new synth_info_data(l, c, e)); }
info_data mk_overload_info(unsigned l, unsigned c, expr const & e) { return info_data(new overload_info_data(l, c, e)); }
info_data mk_coercion_info(unsigned l, unsigned c, expr const & e) { return info_data(new coercion_info_data(l, c, e)); }

bool operator<(info_data const & i1, info_data const & i2) { return i1.compare(i2) < 0; }
bool operator==(info_data const & i1, info_data const & i2) { return i1.compare(i2) == 0; }
bool operator!=(info_data const & i1, info_data const & i2) { return i1.compare(i2) != 0; }
bool operator<(info_data const & i1, info_data_cell const & i2) { return i1.compare(i2) < 0; }

info_manager::info_manager():m_sorted_upto(0) {}

void info_manager::sort_core() {
    if (m_sorted_upto == m_data.size())
        return;
    std::stable_sort(m_data.begin() + m_sorted_upto, m_data.end());
    m_sorted_upto = m_data.size();
}

/**
   \brief Return index i <= m_sorted_upto s.t.
      * forall j < i, m_data[j].pos < (line, column)
      * forall i <= j < m_sorted_upto,  m_data[j].pos >= (line, column)
*/
unsigned info_manager::find(unsigned line, unsigned column) {
    tmp_info_data d(line, column);
    unsigned low  = 0;
    unsigned high = m_sorted_upto;
    while (true) {
        // forall j < low,                    m_data[j] < d
        // forall high <= j < m_sorted_upto,  m_data[j] >= d
        lean_assert(low <= high);
        if (low == high)
            return low;
        unsigned mid = low + ((high - low)/2);
        lean_assert(low <= mid && mid < high);
        lean_assert(mid < m_sorted_upto);
        info_data const & dmid = m_data[mid];
        if (dmid < d) {
            low  = mid+1;
        } else {
            high = mid;
        }
    }
}

void info_manager::invalidate(unsigned sline) {
    lock_guard<mutex> lc(m_mutex);
    sort_core();
    unsigned i = find(sline, 0);
    m_data.resize(i);
    if (m_data.size() < m_sorted_upto)
        m_sorted_upto = m_data.size();
}

void info_manager::add_core(info_data const & d) {
    if (m_data.empty()) {
        m_sorted_upto = 1;
    } else if (m_sorted_upto == m_data.size() && m_data.back() < d) {
        m_sorted_upto++;
    } else if (m_sorted_upto > 0 && d < m_data[m_sorted_upto-1]) {
        m_sorted_upto = find(d.get_line(), d.get_column());
    }
    m_data.push_back(d);
}

void info_manager::add(info_data const & d) {
    lock_guard<mutex> lc(m_mutex);
    add_core(d);
}

void info_manager::append(std::vector<info_data> & vs, bool remove_duplicates) {
    lock_guard<mutex> lc(m_mutex);
    std::stable_sort(vs.begin(), vs.end());
    info_data prev;
    bool first = true;
    for (auto const & v : vs) {
        if (!remove_duplicates || first || v != prev) {
            prev = v;
            add_core(v);
            first = false;
        }
    }
}

void info_manager::sort() {
    lock_guard<mutex> lc(m_mutex);
    sort_core();
}

void info_manager::display(io_state_stream const & ios, unsigned line) {
    lock_guard<mutex> lc(m_mutex);
    sort_core();
    unsigned i = find(line, 0);
    for (; i < m_data.size(); i++) {
        auto const & d = m_data[i];
        if (d.get_line() > line)
            break;
        d.display(ios);
    }
}
}
