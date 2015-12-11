/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include <set>
#include "util/thread.h"
#include "kernel/environment.h"
#include "library/choice.h"
#include "library/scoped_ext.h"
#include "library/pp_options.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/info_manager.h"

namespace lean {
class info_data;

enum class info_kind { Type = 0, ExtraType, Synth, Overload, Coercion, Symbol, Identifier, ProofState };
bool operator<(info_kind k1, info_kind k2) { return static_cast<unsigned>(k1) < static_cast<unsigned>(k2); }

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
    /** \brief Return true iff the information is considered "cheap"
        If the column number is not provided in the method info_manager::display,
        then only "cheap" information is displayed.
    */
    virtual bool is_cheap() const { return true; }
    virtual info_kind kind() const = 0;
    unsigned get_column() const { return m_column; }
    virtual void display(io_state_stream const & ios, unsigned line) const = 0;
    virtual int compare(info_data_cell const & d) const {
        if (m_column != d.m_column)
            return m_column < d.m_column ? -1 : 1;
        if (kind() != d.kind())
            return kind() < d.kind() ? -1 : 1;
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
    bool is_cheap() const { return m_ptr->is_cheap(); }
    void display(io_state_stream const & ios, unsigned line) const { m_ptr->display(ios, line); }
    info_data_cell const * raw() const { return m_ptr; }
    info_kind kind() const { return m_ptr->kind(); }
};

struct tmp_info_data : public info_data_cell {
    tmp_info_data(unsigned c):info_data_cell(c) {}
    virtual info_kind kind() const { lean_unreachable(); }
    virtual void display(io_state_stream const &, unsigned) const { lean_unreachable(); } // LCOV_EXCL_LINE
};

static info_data * g_dummy = nullptr;
void initialize_info_manager() {
    g_dummy = new info_data(new tmp_info_data(0));
}

void finalize_info_manager() {
    delete g_dummy;
}

info_data::info_data():info_data(*g_dummy) {}

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

    virtual info_kind kind() const { return info_kind::Type; }

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

class extra_type_info_data : public info_data_cell {
protected:
    expr m_expr;
    expr m_type;
public:
    extra_type_info_data() {}
    extra_type_info_data(unsigned c, expr const & e, expr const & t):info_data_cell(c), m_expr(e), m_type(t) {}

    virtual info_kind kind() const { return info_kind::ExtraType; }
    virtual bool is_cheap() const { return false; }

    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- EXTRA_TYPE|" << line << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "--" << endl;
        ios << m_type << endl;
        ios << "-- ACK" << endl;
    }

    virtual info_data_cell * instantiate(substitution & s) const {
        expr e = s.instantiate(m_expr);
        expr t = s.instantiate(m_type);
        return is_eqp(e, m_expr) && is_eqp(t, m_type) ? nullptr : new extra_type_info_data(get_column(), e, t);
    }
};

class synth_info_data : public type_info_data {
public:
    synth_info_data(unsigned c, expr const & e):type_info_data(c, e) {}

    virtual info_kind kind() const { return info_kind::Synth; }

    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- SYNTH|" << line << "|" << get_column() << "\n";
        ios << m_expr << endl;
        ios << "-- ACK" << endl;
    }

    virtual info_data_cell * instantiate(substitution & s) const {
        expr e = s.instantiate(m_expr);
        return is_eqp(e, m_expr) ? nullptr : new synth_info_data(get_column(), e);
    }

    expr const & get_expr() const { return m_expr; }
};

class overload_info_data : public info_data_cell {
    expr m_choices;
public:
    overload_info_data(unsigned c, expr const & e):info_data_cell(c), m_choices(e) {}

    virtual info_kind kind() const { return info_kind::Overload; }

    virtual void display(io_state_stream const & ios, unsigned line) const {
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

    virtual void display(io_state_stream const & ios, unsigned line) const {
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

    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- COERCION|" << line << "|" << get_column() << "\n";
        options os = ios.get_options();
        os = os.update_if_undef(get_pp_coercions_name(), true);
        ios.update_options(os) << m_expr << endl << "--" << endl << m_type << endl;
        ios << "-- ACK" << endl;
    }

    virtual info_data_cell * instantiate(substitution & s) const {
        expr e = s.instantiate(m_expr);
        expr t = s.instantiate(m_type);
        return is_eqp(e, m_expr) && is_eqp(t, m_type) ? nullptr : new coercion_info_data(get_column(), e, t);
    }
};

class symbol_info_data : public info_data_cell {
    name m_symbol;
public:
    symbol_info_data(unsigned c, name const & s):info_data_cell(c), m_symbol(s) {}

    virtual info_kind kind() const { return info_kind::Symbol; }

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

    virtual info_kind kind() const { return info_kind::Identifier; }

    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- IDENTIFIER|" << line << "|" << get_column() << "\n";
        ios << m_full_id << "\n";
        ios << "-- ACK" << endl;
    }
};

class proof_state_info_data : public info_data_cell {
    proof_state m_ps;
public:
    proof_state_info_data(unsigned c, proof_state const & ps):info_data_cell(c), m_ps(ps) {}
    virtual info_kind kind() const { return info_kind::ProofState; }
    virtual bool is_cheap() const { return false; }
    virtual void display(io_state_stream const & ios, unsigned line) const {
        ios << "-- PROOF_STATE|" << line << "|" << get_column() << "\n";
        bool first = true;
        substitution s = m_ps.get_subst();
        for (goal const & g : m_ps.get_goals()) {
            if (first)
                first = false;
            else
                ios << "--" << endl;
            ios << g.instantiate(s) << endl;
        }
        ios << "-- ACK" << endl;
    }
};

info_data mk_type_info(unsigned c, expr const & e) { return info_data(new type_info_data(c, e)); }
info_data mk_extra_type_info(unsigned c, expr const & e, expr const & t) { return info_data(new extra_type_info_data(c, e, t)); }
info_data mk_synth_info(unsigned c, expr const & e) { return info_data(new synth_info_data(c, e)); }
info_data mk_overload_info(unsigned c, expr const & e) { return info_data(new overload_info_data(c, e)); }
info_data mk_overload_notation_info(unsigned c, list<expr> const & a) { return info_data(new overload_notation_info_data(c, a)); }
info_data mk_coercion_info(unsigned c, expr const & e, expr const & t) { return info_data(new coercion_info_data(c, e, t)); }
info_data mk_symbol_info(unsigned c, name const & s) { return info_data(new symbol_info_data(c, s)); }
info_data mk_identifier_info(unsigned c, name const & full_id) { return info_data(new identifier_info_data(c, full_id)); }
info_data mk_proof_state_info(unsigned c, proof_state const & ps) { return info_data(new proof_state_info_data(c, ps)); }

struct info_data_cmp {
    int operator()(info_data const & i1, info_data const & i2) const { return i1.compare(i2); }
};

struct info_manager::imp {
    typedef rb_tree<info_data, info_data_cmp> info_data_set;
    /** \brief Saved environment + options for a given line and iteration
        Whenever "lean server" starts processing a file again, we bump the iteration.
    */
    struct env_info {
        unsigned         m_line;
        unsigned         m_column;
        mutable unsigned m_iteration;
        environment      m_env;
        options          m_options;
        env_info():m_line(0), m_iteration(0) {}
        env_info(unsigned l, unsigned c, unsigned i, environment const & env, options const & o):
            m_line(l), m_column(c), m_iteration(i), m_env(env), m_options(o) {}
        friend bool operator<(env_info const & i1, env_info const & i2) {
            if (i1.m_line != i2.m_line)
                return i1.m_line < i2.m_line;
            return i1.m_column < i2.m_column;
        }
    };
    mutex                      m_mutex;
    bool                       m_block_new_info;
    std::vector<info_data_set> m_line_data;
    std::vector<bool>          m_line_valid;
    std::set<env_info>         m_env_info;
    unsigned                   m_iteration; // current interation
    unsigned                   m_processed_upto;

    imp():m_block_new_info(false), m_iteration(0), m_processed_upto(0) {}

    void block_new_info(bool f) {
        lock_guard<mutex> lc(m_mutex);
        m_block_new_info = f;
    }

    void synch_line(unsigned l) {
        lean_assert(l > 0);
        if (l >= m_line_data.size()) {
            m_line_data.resize(l+1);
            m_line_valid.resize(l+1, false);
        }
    }

    void save_environment_options(unsigned l, unsigned c, environment const & env, options const & o) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        // erase all entries in m_env_info such that e.m_line <= l and e.m_column <= c and e.m_iteration < m_iteration
        auto it  = m_env_info.begin();
        auto end = m_env_info.end();
        while (it != end) {
            if (it->m_line > l || (it->m_line == l && it->m_column > c)) {
                break;
            } else if ((it->m_line < l || (it->m_line == l && it->m_column <= c)) &&
                       it->m_iteration < m_iteration) {
                m_env_info.erase(it++);
            } else {
                ++it;
            }
        }
        env_info info(l, c, m_iteration, env, o);
        m_env_info.erase(info);
        m_env_info.insert(info);
    }

    static bool is_tactic_type(expr const & e) {
        expr const * it = &e;
        while (is_pi(*it)) {
            it = &binding_body(*it);
        }
        return *it == get_tactic_type() || *it == get_tactic_expr_type() || *it == get_tactic_expr_list_type();
    }

    void add_type_info(unsigned l, unsigned c, expr const & e) {
        if (is_tactic_type(e))
            return;
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_type_info(c, e));
    }

    void add_extra_type_info(unsigned l, unsigned c, expr const & e, expr const & t) {
        if (is_tactic_type(t))
            return;
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_extra_type_info(c, e, t));
    }

    void add_synth_info(unsigned l, unsigned c, expr const & e) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_synth_info(c, e));
    }

    void add_overload_info(unsigned l, unsigned c, expr const & e) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_overload_info(c, e));
    }

    void add_overload_notation_info(unsigned l, unsigned c, list<expr> const & a) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_overload_notation_info(c, a));
    }

    void add_coercion_info(unsigned l, unsigned c, expr const & e, expr const & t) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_coercion_info(c, e, t));
    }

    void erase_coercion_info(unsigned l, unsigned c) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].erase(mk_coercion_info(c, expr(), expr()));
    }

    void add_symbol_info(unsigned l, unsigned c, name const & s) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_symbol_info(c, s));
    }

    static bool is_tactic_id(name const & id) {
        if (id.is_atomic())
            return id == get_tactic_name();
        else
            return is_tactic_id(id.get_prefix());
    }

    void add_identifier_info(unsigned l, unsigned c, name const & full_id) {
        if (is_tactic_id(full_id))
            return;
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_identifier_info(c, full_id));
    }

    void add_proof_state_info(unsigned l, unsigned c, proof_state const & ps) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        m_line_data[l].insert(mk_proof_state_info(c, ps));
    }

    void remove_proof_state_info(unsigned start_line, unsigned start_col, unsigned end_line, unsigned end_col) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info || m_line_data.empty())
            return;
        if (end_line >= m_line_data.size())
            end_line = m_line_data.size() - 1;
        for (unsigned i = start_line; i <= end_line; i++) {
            info_data_set const & curr_set = m_line_data[i];
            if (curr_set.find_if([](info_data const & info) { return info.kind() == info_kind::ProofState; })) {
                info_data_set new_curr_set;
                curr_set.for_each([&](info_data const & info) {
                        if (info.kind() == info_kind::ProofState) {
                            if ((i == start_line && info.get_column() < start_col) ||
                                (i == end_line && info.get_column() >= end_col))
                                new_curr_set.insert(info);
                        } else {
                            new_curr_set.insert(info);
                        }
                    });
                m_line_data[i] = new_curr_set;
            }
        }
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
        if (m_block_new_info)
            return;
        substitution tmp_s = s;
        unsigned sz     = m_line_data.size();
        for (unsigned i = 0; i < sz; i++) {
            m_line_data[i] = instantiate(m_line_data[i], tmp_s);
        }
    }

    void merge(info_manager::imp const & m, bool overwrite) {
        if (m.m_line_data.empty())
            return;
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        unsigned sz = m.m_line_data.size();
        for (unsigned i = 1; i < sz; i++) {
            info_data_set s = m.m_line_data[i];
            if (s.empty())
                continue;
            synch_line(i);
            if (!overwrite && m_line_valid[i])
                continue;
            s.for_each([&](info_data const & d) {
                    if (overwrite || !m_line_data[i].contains(d))
                        m_line_data[i].insert(d);
                });
        }
    }

    void insert_line(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        lean_assert(m_line_data.size() == m_line_valid.size());
        synch_line(l);
        if (m_processed_upto > l - 1)
            m_processed_upto = l - 1;
        m_line_data.push_back(info_data_set());
        m_line_valid.push_back(false);
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
        lean_assert(m_line_data.size() == m_line_valid.size());
        lean_assert(l > 0);
        if (l >= m_line_data.size())
            return;
        lean_assert(!m_line_data.empty());
        for (unsigned i = l; i < m_line_data.size() - 1; i++) {
            m_line_data[i]  = m_line_data[i+1];
            m_line_valid[i] = m_line_valid[i+1];
        }
        m_line_data.pop_back();
        m_line_valid.pop_back();
        if (m_processed_upto > l - 1)
            m_processed_upto = l - 1;
    }

    void invalidate_line_col_core(unsigned l, optional<unsigned> const & c) {
        lock_guard<mutex> lc(m_mutex);
        lean_assert(m_line_data.size() == m_line_valid.size());
        synch_line(l);
        if (m_processed_upto > l - 1)
            m_processed_upto = l - 1;
        if (!c) {
            m_line_data[l]  = info_data_set();
        } else {
            info_data_set new_set;
            m_line_data[l].for_each([&](info_data const & d) {
                    if (d.get_column() < *c)
                        new_set.insert(d);
                });
            m_line_data[l] = new_set;
        }
        m_line_valid[l] = false;
    }

    void invalidate_line(unsigned l) {
        invalidate_line_col_core(l, optional<unsigned>());
    }

    void invalidate_line_col(unsigned l, unsigned c) {
        invalidate_line_col_core(l, optional<unsigned>(c));
    }

    void set_processed_upto(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        synch_line(l);
        m_processed_upto = l;
    }

    void start_from(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        m_iteration++;
        synch_line(l);
        m_processed_upto = l;
        for (auto it = m_env_info.begin(); it != m_env_info.end(); ++it) {
            if (it->m_line < l)
                it->m_iteration = m_iteration;
            else
                break;
        }
        m_block_new_info = false;
    }

    void commit_upto(unsigned l, bool valid) {
        lock_guard<mutex> lc(m_mutex);
        if (m_block_new_info)
            return;
        synch_line(l);
        for (unsigned i = m_processed_upto; i < l && i < m_line_valid.size(); i++)
            m_line_valid[i] = valid;
        m_processed_upto = l;
    }

    bool is_invalidated(unsigned l) {
        lock_guard<mutex> lc(m_mutex);
        lean_assert(m_line_data.size() == m_line_valid.size());
        if (l >= m_line_valid.size())
            return true;
        return !m_line_valid[l];
    }

    void display_core(environment const & env, options const & o, io_state const & ios, unsigned line,
                      optional<unsigned> const & col) {
        m_line_data[line].for_each([&](info_data const & d) {
                io_state_stream out = regular(env, ios).update_options(o);
                if ((!col && d.is_cheap()) || (col && d.get_column() == *col))
                    d.display(out, line);
            });
    }

    void display(environment const & env, io_state const & ios, unsigned line, optional<unsigned> const & col) {
        lock_guard<mutex> lc(m_mutex);
        if (line >= m_line_data.size() || m_line_data[line].empty()) {
            // do nothing
        } else if (m_env_info.empty()) {
            display_core(env, ios.get_options(), ios, line, col);
        } else {
            auto it  = m_env_info.begin();
            auto end = m_env_info.end();
            lean_assert(it != end);
            if (it->m_line > line) {
                display_core(env, ios.get_options(), ios, line, col);
                return;
            }
            while (true) {
                lean_assert(it->m_line <= line);
                lean_assert(it != end);
                auto next = it;
                ++next;
                if (next == end || next->m_line > line) {
                    display_core(it->m_env, join(it->m_options, ios.get_options()), ios, line, col);
                    return;
                }
                it = next;
            }
        }
    }

    optional<pair<environment, options>> get_final_env_opts() {
        lock_guard<mutex> lc(m_mutex);
        if (m_env_info.empty()) {
            return optional<pair<environment, options>>();
        } else {
            auto it = m_env_info.end();
            --it;
            return optional<pair<environment, options>>(mk_pair(it->m_env, it->m_options));
        }
    }

    optional<pair<environment, options>> get_closest_env_opts(unsigned linenum) {
        lock_guard<mutex> lc(m_mutex);
        auto it = m_env_info.begin();
        if (it == m_env_info.end())
            return optional<pair<environment, options>>();
        if (it->m_line > linenum)
            return optional<pair<environment, options>>(it->m_env, it->m_options);
        while (true) {
            lean_assert(it != m_env_info.end() && it->m_line <= linenum);
            auto next = it;
            next++;
            if (next == m_env_info.end())
                return optional<pair<environment, options>>(mk_pair(it->m_env, it->m_options));
            if (next->m_line > linenum)
                return optional<pair<environment, options>>(mk_pair(next->m_env, next->m_options));
            it = next;
        }
    }

    optional<expr> get_type_at(unsigned line, unsigned col) {
        lock_guard<mutex> lc(m_mutex);
        if (line >= m_line_data.size())
            return none_expr();
        if (auto it = m_line_data[line].find(mk_type_info(col, expr())))
            return some_expr(static_cast<type_info_data const *>(it->raw())->get_type());
        else
            return none_expr();
    }

    optional<expr> get_meta_at(unsigned line, unsigned col) {
        lock_guard<mutex> lc(m_mutex);
        if (line >= m_line_data.size())
            return none_expr();
        if (auto it = m_line_data[line].find(mk_synth_info(col, expr())))
            return some_expr(static_cast<synth_info_data const *>(it->raw())->get_expr());
        else
            return none_expr();
    }

    unsigned get_processed_upto() {
        lock_guard<mutex> lc(m_mutex);
        return m_processed_upto;
    }

    void clear() {
        lock_guard<mutex> lc(m_mutex);
        m_line_data.clear();
        m_line_valid.clear();
        m_env_info.clear();
        m_iteration      = 0;
        m_processed_upto = 0;
    }
};

info_manager::info_manager():m_ptr(new imp()) {}
info_manager::~info_manager() {}
void info_manager::add_type_info(unsigned l, unsigned c, expr const & e) { m_ptr->add_type_info(l, c, e); }
void info_manager::add_extra_type_info(unsigned l, unsigned c, expr const & e, expr const & t) { m_ptr->add_extra_type_info(l, c, e, t); }
void info_manager::add_synth_info(unsigned l, unsigned c, expr const & e) { m_ptr->add_synth_info(l, c, e); }
void info_manager::add_overload_info(unsigned l, unsigned c, expr const & e) { m_ptr->add_overload_info(l, c, e); }
void info_manager::add_overload_notation_info(unsigned l, unsigned c, list<expr> const & a) { m_ptr->add_overload_notation_info(l, c, a); }
void info_manager::add_coercion_info(unsigned l, unsigned c, expr const & e, expr const & t) { m_ptr->add_coercion_info(l, c, e, t); }
void info_manager::erase_coercion_info(unsigned l, unsigned c) { m_ptr->erase_coercion_info(l, c); }
void info_manager::add_symbol_info(unsigned l, unsigned c, name const & s) { m_ptr->add_symbol_info(l, c, s); }
void info_manager::add_identifier_info(unsigned l, unsigned c, name const & full_id) {
    m_ptr->add_identifier_info(l, c, full_id);
}
void info_manager::add_proof_state_info(unsigned l, unsigned c, proof_state const & ps) {
    m_ptr->add_proof_state_info(l, c, ps);
}
void info_manager::instantiate(substitution const & s) { m_ptr->instantiate(s); }
void info_manager::merge(info_manager const & m, bool overwrite) { m_ptr->merge(*m.m_ptr, overwrite); }
void info_manager::insert_line(unsigned l) { m_ptr->insert_line(l); }
void info_manager::remove_line(unsigned l) { m_ptr->remove_line(l); }
void info_manager::invalidate_line(unsigned l) { m_ptr->invalidate_line(l); }
void info_manager::invalidate_line_col(unsigned l, unsigned c) { m_ptr->invalidate_line_col(l, c); }
void info_manager::commit_upto(unsigned l, bool valid) { m_ptr->commit_upto(l, valid); }
void info_manager::set_processed_upto(unsigned l) { m_ptr->set_processed_upto(l); }
bool info_manager::is_invalidated(unsigned l) const { return m_ptr->is_invalidated(l); }
void info_manager::save_environment_options(unsigned l, unsigned c, environment const & env, options const & o) {
    m_ptr->save_environment_options(l, c, env, o);
}
void info_manager::clear() { m_ptr->clear(); }
optional<pair<environment, options>> info_manager::get_final_env_opts() const { return m_ptr->get_final_env_opts(); }
optional<pair<environment, options>> info_manager::get_closest_env_opts(unsigned linenum) const { return m_ptr->get_closest_env_opts(linenum); }
void info_manager::display(environment const & env, io_state const & ios, unsigned line, optional<unsigned> const & col) const {
    m_ptr->display(env, ios, line, col);
}
unsigned info_manager::get_processed_upto() const { return m_ptr->m_processed_upto; }
optional<expr> info_manager::get_type_at(unsigned line, unsigned col) const { return m_ptr->get_type_at(line, col); }
optional<expr> info_manager::get_meta_at(unsigned line, unsigned col) const { return m_ptr->get_meta_at(line, col); }
void info_manager::block_new_info() { m_ptr->block_new_info(true); }
void info_manager::start_from(unsigned l) { m_ptr->start_from(l); }
void info_manager::remove_proof_state_info(unsigned start_line, unsigned start_col, unsigned end_line, unsigned end_col) {
    m_ptr->remove_proof_state_info(start_line, start_col, end_line, end_col);
}
}
