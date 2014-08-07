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
struct tmp_info_data : public info_data {
    tmp_info_data(unsigned l, unsigned c):info_data(l, c) {}
    virtual void display(io_state_stream const &) const { lean_unreachable(); } // LCOV_EXCL_LINE
};

bool operator<(info_data const & i1, info_data const & i2) {
    if (i1.get_line() != i2.get_line())
        return i1.get_line() < i2.get_line();
    else
        return i1.get_column() < i2.get_column();
}

void type_info_data::display(io_state_stream const & ios) const {
    ios << "-- TYPE|" << get_line() << "|" << get_column() << "\n";
    ios << m_expr << endl;
    ios << "-- ACK" << endl;
}

void overload_info_data::display(io_state_stream const & ios) const {
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

void coercion_info_data::display(io_state_stream const & ios) const {
    ios << "-- COERCION|" << get_line() << "|" << get_column() << "\n";
    options os = ios.get_options();
    os = os.update(get_pp_coercion_option_name(), true);
    ios.update_options(os) << m_coercion << endl;
    ios << "-- ACK" << endl;
}

info_manager::info_manager():m_sorted_upto(0) {}

void info_manager::sort_core() {
    if (m_sorted_upto == m_data.size())
        return;
    std::stable_sort(m_data.begin() + m_sorted_upto, m_data.end(),
                     [](std::unique_ptr<info_data> const & i1, std::unique_ptr<info_data> const & i2) { return *i1 < *i2; });
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
        info_data const & dmid = *m_data[mid];
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

void info_manager::add_core(std::unique_ptr<info_data> && d) {
    if (m_data.empty()) {
        m_sorted_upto = 1;
    } else if (m_sorted_upto == m_data.size() && *m_data.back() < *d) {
        m_sorted_upto++;
    } else if (m_sorted_upto > 0 && *d < *m_data[m_sorted_upto-1]) {
        m_sorted_upto = find(d->get_line(), d->get_column());
    }
    m_data.push_back(std::move(d));
}

void info_manager::add(std::unique_ptr<info_data> && d) {
    lock_guard<mutex> lc(m_mutex);
    add_core(std::move(d));
}

void info_manager::append(std::vector<std::unique_ptr<info_data>> && v) {
    lock_guard<mutex> lc(m_mutex);
    for (auto & d : v)
        add_core(std::move(d));
}

void info_manager::append(std::vector<type_info_data> & v, bool remove_duplicates) {
    lock_guard<mutex> lc(m_mutex);
    std::stable_sort(v.begin(), v.end());
    type_info_data prev;
    bool first = true;
    for (auto const & p : v) {
        if (!remove_duplicates || first || !p.eq_pos(prev.get_line(), prev.get_column())) {
            add_core(std::unique_ptr<info_data>(new type_info_data(p)));
            prev  = p;
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
        auto const & d = *m_data[i];
        if (d.get_line() > line)
            break;
        d.display(ios);
    }
}
}
