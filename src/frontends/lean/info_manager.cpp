/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include "util/thread.h"
#include "library/choice.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/pp_options.h"

namespace lean {
class info_data;

class info_data_cell {
    unsigned m_column;
    MK_LEAN_RC();
    void dealloc() { delete this; }
protected:
    friend info_data;
    virtual info_data_cell * instantiate(substitution &) const { return nullptr; }
public:
    info_data_cell():m_column(0), m_rc(0) {}
    info_data_cell(unsigned c):m_column(c), m_rc(0) {}
    virtual ~info_data_cell() {}
    unsigned get_column() const { return m_column; }
    virtual void display(io_state_stream const & ios, unsigned line) const = 0;
    virtual int compare(info_data_cell const & d) const {
        if (m_column != d.m_column)
            return m_column < d.m_column ? -1 : 1;
        if (typeid(*this) != typeid(d))
            return typeid(*this).before(typeid(d)) ? -1 : 1;
        return 0;
    }
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
    int compare(info_data const & d) const { return m_ptr->compare(*d.m_ptr); }
    int compare(info_data_cell const & d) const { return m_ptr->compare(d); }
    info_data instantiate(substitution & s) const;
    unsigned get_column() const { return m_ptr->get_column(); }
    void display(io_state_stream const & ios, unsigned line) const { m_ptr->display(ios, line); }
};

struct tmp_info_data : public info_data_cell {
    tmp_info_data(unsigned c):info_data_cell(c) {}
    virtual void display(io_state_stream const &, unsigned) const { lean_unreachable(); } // LCOV_EXCL_LINE
};

static info_data g_dummy(new tmp_info_data(0));
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
    type_info_data(unsigned c, expr const & e):info_data_cell(c), m_expr(e) {}

    expr const & get_type() const { return m_expr; }

    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- TYPE|" << line << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "-- ACK" << endl;
    }

    virtual info_data_cell * instantiate(substitution & s) const {
        expr e = s.instantiate(m_expr);
        return is_eqp(e, m_expr) ? nullptr : new type_info_data(get_column(), e);
    }
};

class synth_info_data : public type_info_data {
public:
    synth_info_data(unsigned c, expr const & e):type_info_data(c, e) {}
    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- SYNTH|" << line << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "-- ACK" << endl;
    }

    virtual info_data_cell * instantiate(substitution & s) const {
        expr e = s.instantiate(m_expr);
        return is_eqp(e, m_expr) ? nullptr : new synth_info_data(get_column(), e);
    }
};

class overload_info_data : public info_data_cell {
    expr m_choices;
public:
    overload_info_data(unsigned c, expr const & e):info_data_cell(c), m_choices(e) {}
    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- OVERLOAD|" << line << "|" << get_column() << "\n";
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
    coercion_info_data(unsigned c, expr const & e):info_data_cell(c), m_coercion(e) {}
    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- COERCION|" << line << "|" << get_column() << "\n";
        options os = ios.get_options();
        os = os.update(get_pp_coercion_option_name(), true);
        ios.update_options(os) << m_coercion << endl;
        ios << "-- ACK" << endl;
    }
};

class symbol_info_data : public info_data_cell {
    name m_symbol;
public:
    symbol_info_data(unsigned c, name const & s):info_data_cell(c), m_symbol(s) {}
    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- SYMBOL|" << line << "|" << get_column() << "\n";
        ios << m_symbol << "\n";
        ios << "-- ACK" << endl;
    }
};

class identifier_info_data : public info_data_cell {
    name m_full_id;
public:
    identifier_info_data(unsigned c, name const & full_id):info_data_cell(c), m_full_id(full_id) {}
    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- IDENTIFIER|" << line << "|" << get_column() << "\n";
        ios << m_full_id << "\n";
        ios << "-- ACK" << endl;
    }
};

info_data mk_type_info(unsigned c, expr const & e) { return info_data(new type_info_data(c, e)); }
info_data mk_synth_info(unsigned c, expr const & e) { return info_data(new synth_info_data(c, e)); }
info_data mk_overload_info(unsigned c, expr const & e) { return info_data(new overload_info_data(c, e)); }
info_data mk_coercion_info(unsigned c, expr const & e) { return info_data(new coercion_info_data(c, e)); }
info_data mk_symbol_info(unsigned c, name const & s) { return info_data(new symbol_info_data(c, s)); }
info_data mk_identifier_info(unsigned c, name const & full_id) { return info_data(new identifier_info_data(c, full_id)); }

struct info_data_cmp {
    int operator()(info_data const & i1, info_data const & i2) const { return i1.compare(i2); }
};

struct info_manager::imp {
    typedef rb_tree<info_data, info_data_cmp> info_data_set;
    mutex                      m_mutex;
    std::vector<info_data_set> m_line_data;
    std::vector<bool>          m_line_valid;
    unsigned                   m_available_upto;

    imp():m_available_upto(0) {}

    void synch_line(unsigned l) {
        lean_assert(l > 0);
        if (l >= m_line_data.size()) {
            m_line_data.resize(l+1);
            m_line_valid.resize(l+1, true);
        }
    }

    void add_type_info(unsigned l, unsigned c, expr const & e) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        m_line_data[l].insert(mk_type_info(c, e));
    }

    void add_synth_info(unsigned l, unsigned c, expr const & e) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        m_line_data[l].insert(mk_synth_info(c, e));
    }

    void add_overload_info(unsigned l, unsigned c, expr const & e) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        m_line_data[l].insert(mk_overload_info(c, e));
    }

    void add_coercion_info(unsigned l, unsigned c, expr const & e) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        m_line_data[l].insert(mk_coercion_info(c, e));
    }

    void add_symbol_info(unsigned l, unsigned c, name const & s) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        m_line_data[l].insert(mk_symbol_info(c, s));
    }

    void add_identifier_info(unsigned l, unsigned c, name const & full_id) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        m_line_data[l].insert(mk_identifier_info(c, full_id));
    }

    static info_data_set instantiate(info_data_set const & s, substitution & subst) {
        info_data_set r;
        s.for_each([&](info_data const & d) {
                r.insert(d.instantiate(subst));
            });
        return r;
    }

    void instantiate(substitution const & s) {
        lock_guard<mutex> lc(m_mutex);
        substitution tmp_s = s;
        unsigned sz     = m_line_data.size();
        for (unsigned i = 0; i < sz; i++) {
            m_line_data[i] = instantiate(m_line_data[i], tmp_s);
        }
    }

    void merge(info_manager::imp const & m) {
        if (m.m_line_data.empty())
            return;
        lock_guard<mutex> lc(m_mutex);
        unsigned sz = m.m_line_data.size();
        for (unsigned i = 1; i < sz; i++) {
            info_data_set const & s = m.m_line_data[i];
            s.for_each([&](info_data const & d) {
                    synch_line(i);
                    m_line_data[i].insert(d);
                });
        }
    }

    void insert_line(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        if (m_available_upto > l - 1)
            m_available_upto = l - 1;
        m_line_data.push_back(info_data_set());
        unsigned i = m_line_data.size();
        while (i > l) {
            --i;
            m_line_data[i]  = m_line_data[i-1];
            m_line_valid[i] = m_line_valid[i-1];
        }
        m_line_valid[l] = false;
    }

    void remove_line(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        lean_assert(l > 0);
        if (l >= m_line_data.size())
            return;
        lean_assert(!m_line_data.empty());
        for (unsigned i = l; i < m_line_data.size() - 1; i++) {
            m_line_data[i]  = m_line_data[i+1];
            m_line_valid[i] = m_line_valid[i+1];
        }
        m_line_data.pop_back();
        if (m_available_upto > l - 1)
            m_available_upto = l - 1;
    }

    void invalidate_line(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        if (m_available_upto > l - 1)
            m_available_upto = l - 1;
        m_line_data[l]  = info_data_set();
        m_line_valid[l] = false;
    }

    void commit_upto(unsigned l, bool valid) {
        lock_guard<mutex> lc(m_mutex);
        for (unsigned i = m_available_upto; i < l && i < m_line_valid.size(); i++)
            m_line_valid[i] = valid;
        m_available_upto = l;
    }

    bool is_available(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        return l < m_available_upto;
    }

    bool is_invalidated(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        if (l >= m_line_valid.size())
            return false;
        return !m_line_valid[l];
    }

    void display(io_state_stream const & ios, unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        if (l >= m_line_data.size())
            return;
        m_line_data[l].for_each([&](info_data const & d) {
                d.display(ios, l);
            });
    }

    void clear() {
        lock_guard<mutex> lc(m_mutex);
        m_line_data.clear();
    }
};

info_manager::info_manager():m_ptr(new imp()) {}
info_manager::~info_manager() {}
void info_manager::add_type_info(unsigned l, unsigned c, expr const & e) { m_ptr->add_type_info(l, c, e); }
void info_manager::add_synth_info(unsigned l, unsigned c, expr const & e) { m_ptr->add_synth_info(l, c, e); }
void info_manager::add_overload_info(unsigned l, unsigned c, expr const & e) { m_ptr->add_overload_info(l, c, e); }
void info_manager::add_coercion_info(unsigned l, unsigned c, expr const & e) { m_ptr->add_coercion_info(l, c, e); }
void info_manager::add_symbol_info(unsigned l, unsigned c, name const & s) { m_ptr->add_symbol_info(l, c, s); }
void info_manager::add_identifier_info(unsigned l, unsigned c, name const & full_id) {
    m_ptr->add_identifier_info(l, c, full_id);
}
void info_manager::instantiate(substitution const & s) { m_ptr->instantiate(s); }
void info_manager::merge(info_manager const & m) { m_ptr->merge(*m.m_ptr); }
void info_manager::insert_line(unsigned l) { m_ptr->insert_line(l); }
void info_manager::remove_line(unsigned l) { m_ptr->remove_line(l); }
void info_manager::invalidate_line(unsigned l) { m_ptr->invalidate_line(l); }
void info_manager::commit_upto(unsigned l, bool valid) { m_ptr->commit_upto(l, valid); }
bool info_manager::is_available(unsigned l) const { return m_ptr->is_available(l); }
bool info_manager::is_invalidated(unsigned l) const { return m_ptr->is_invalidated(l); }
void info_manager::clear() { m_ptr->clear(); }
void info_manager::display(io_state_stream const & ios, unsigned line) { m_ptr->display(ios, line); }
}
