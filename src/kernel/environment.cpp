/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include <limits>
#include <atomic>
#include <sstream>
#include <unordered_map>
#include "environment.h"
#include "type_check.h"
#include "exception.h"
#include "debug.h"

namespace lean {
constexpr unsigned uninit = std::numeric_limits<int>::max();

environment::definition::definition(name const & n, expr const & t, expr const & v, bool opaque):
    m_name(n),
    m_type(t),
    m_value(v),
    m_opaque(opaque) {
}

environment::definition::~definition() {
}

environment::object_kind environment::definition::kind() const {
    return object_kind::Definition;
}

void environment::definition::display(std::ostream & out) const {
    out << "Definition " << m_name << " : " << m_type << " := " << m_value << "\n";
}

environment::fact::fact(name const & n, expr const & t):
    m_name(n),
    m_type(t) {
}

environment::fact::~fact() {
}

environment::object_kind environment::fact::kind() const {
    return object_kind::Fact;
}

void environment::fact::display(std::ostream & out) const {
    out << "Fact " << m_name << " : " << m_type << "\n";
}

/** \brief Implementation of the Lean environment. */
struct environment::imp {
    typedef std::unordered_map<name, object *, name_hash, name_eq> object_dictionary;
    std::vector<std::vector<unsigned>>   m_uvar_distances;
    std::vector<level>                   m_uvars;
    std::atomic<unsigned>                m_num_children;
    std::shared_ptr<imp>                 m_parent;
    std::vector<object*>                 m_objects;
    object_dictionary                    m_object_dictionary;

    bool has_children() const { return m_num_children > 0; }
    void inc_children() { m_num_children++; }
    void dec_children() { m_num_children--; }

    bool has_parent() const { return m_parent != nullptr; }

    /** \brief Return v - k. It throws an exception if there is a underflow. */
    static int sub(int v, unsigned k) {
        long long r = static_cast<long long>(v) - static_cast<long long>(k);
        if (r < std::numeric_limits<int>::min())
            throw exception("universe overflow");
        return static_cast<int>(r);
    }

    /** \brief Return v + k. It throws an exception if there is an overflow. */
    static int add(int v, unsigned k) {
        long long r = static_cast<long long>(v) + static_cast<long long>(k);
        if (r > std::numeric_limits<int>::max() - 1)
            throw exception("universe overflow");
        return static_cast<int>(r);
    }

    /** \brief Return v + k. It throws an exception if there is an overflow. */
    static unsigned add(unsigned v, unsigned k) {
        unsigned long long r = static_cast<unsigned long long>(v) + static_cast<unsigned long long>(k);
        if (r > std::numeric_limits<int>::max() - 1)
            throw exception("universe overflow");
        return static_cast<unsigned>(r);
    }

    /** \brief Return true iff l1 >= l2 + k */
    bool is_ge(level const & l1, level const & l2, int k) {
        switch (kind(l2)) {
        case level_kind::UVar:
            switch (kind(l1)) {
            case level_kind::UVar: {
                unsigned d = m_uvar_distances[uvar_idx(l1)][uvar_idx(l2)];
                return d != uninit && (k < 0 || (k >= 0 && d >= static_cast<unsigned>(k)));
            }
            case level_kind::Lift: return is_ge(lift_of(l1), l2, sub(k, lift_offset(l1)));
            case level_kind::Max:  return std::any_of(max_begin_levels(l1), max_end_levels(l1), [&](level const & l) { return is_ge(l, l2, k); });
            }
        case level_kind::Lift: return is_ge(l1, lift_of(l2), add(k, lift_offset(l2)));
        case level_kind::Max:  return std::all_of(max_begin_levels(l2), max_end_levels(l2), [&](level const & l) { return is_ge(l1, l, k); });
        }
        lean_unreachable();
        return false;
    }

    bool is_ge(level const & l1, level const & l2) {
        if (has_parent())
            return m_parent->is_ge(l1, l2);
        else
            return is_ge(l1, l2, 0);
    }

    level add_var(name const & n) {
        if (std::any_of(m_uvars.begin(), m_uvars.end(), [&](level const & l){ return uvar_name(l) == n; }))
            throw exception("invalid universe variable declaration, it has already been declared");
        unsigned idx = m_uvars.size();
        level r(n, idx);
        m_uvars.push_back(r);
        std::for_each(m_uvar_distances.begin(), m_uvar_distances.end(), [](std::vector<unsigned> & v) { v.push_back(uninit); });
        m_uvar_distances.push_back(std::vector<unsigned>());
        std::vector<unsigned> & d = m_uvar_distances.back();
        d.resize(m_uvars.size(), static_cast<unsigned>(uninit));
        d[idx] = 0;
        return r;
    }

    void add_constraint(uvar v1, uvar v2, unsigned d) {
        lean_assert(v1 != v2);
        unsigned num = m_uvar_distances.size();
        lean_assert(v1 < num);
        lean_assert(v2 < num);
        std::vector<unsigned> & v1_dists = m_uvar_distances[v1];
        if (v1_dists[v2] == uninit || d >= v1_dists[v2]) {
            v1_dists[v2] = d;
            // update forward
            std::vector<unsigned> & v2_dists = m_uvar_distances[v2];
            for (uvar v3 = 0; v3 < num; v3++) {
                if (v2_dists[v3] != uninit) {
                    lean_assert(v1 != v3);
                    unsigned d_v1_v3 = add(d, v2_dists[v3]);
                    if (v1_dists[v3] == uninit || d_v1_v3 >= v1_dists[v3])
                        v1_dists[v3] = d_v1_v3;
                }
            }
        }
    }

    void add_constraints(uvar v1, level const & l, unsigned k) {
        switch (kind(l)) {
        case level_kind::UVar: add_constraint(v1, uvar_idx(l), k); return;
        case level_kind::Lift: add_constraints(v1, lift_of(l), add(k, lift_offset(l))); return;
        case level_kind::Max:  std::for_each(max_begin_levels(l), max_end_levels(l), [&](level const & l1) { add_constraints(v1, l1, k); }); return;
        }
        lean_unreachable();
    }

    level define_uvar(name const & n, level const & l) {
        if (has_parent())
            throw exception("invalid universe declaration, universe variables can only be declared in top-level environments");
        if (has_children())
            throw exception("invalid universe declaration, environment has children environments");
        level r = add_var(n);
        add_constraints(uvar_idx(r), l, 0);
        return r;
    }

    level get_uvar(name const & n) const {
        if (has_parent()) {
            return m_parent->get_uvar(n);
        } else {
            auto it = std::find_if(m_uvars.begin(), m_uvars.end(), [&](level const & l) { return uvar_name(l) == n; });
            if (it == m_uvars.end()) {
                std::ostringstream s;
                s << "unknown universe variable '" << n << "'";
                throw exception (s.str());
            } else {
                return *it;
            }
        }
    }

    void init_uvars() {
        m_uvars.push_back(level());
        m_uvar_distances.push_back(std::vector<unsigned>());
        m_uvar_distances.back().push_back(0);
        lean_assert(uvar_idx(m_uvars.back()) == 0);
    }

    void display_uvars(std::ostream & out) const {
        std::for_each(m_uvars.begin(), m_uvars.end(),
                      [&](level const & u) {
                          std::vector<unsigned> const & u_dists = m_uvar_distances[uvar_idx(u)];
                          unsigned num = u_dists.size();
                          for (uvar v2 = 0; v2 < num; v2++) {
                              if (v2 != uvar_idx(u) && u_dists[v2] != uninit) {
                                  out << uvar_name(u) << " >= " << uvar_name(m_uvars[v2]);
                                  if (u_dists[v2] > 0)
                                      out << " + " << u_dists[v2];
                                  out << "\n";
                              }
                          }
                      });
    }

    void check_no_children() {
        if (has_children())
            throw exception("invalid object declaration, environment has children environments");
    }

    void check_name(name const & n) {
        if (m_object_dictionary.find(n) != m_object_dictionary.end()) {
            std::ostringstream s;
            s << "environment already contains an object with name '" << n << "'";
            throw exception (s.str());
        }
    }

    void add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
        m_objects.push_back(new definition(n, t, v, opaque));
        m_object_dictionary.insert(std::make_pair(n, m_objects.back()));
    }

    void add_fact(name const & n, expr const & t) {
        m_objects.push_back(new fact(n, t));
        m_object_dictionary.insert(std::make_pair(n, m_objects.back()));
    }

    object const * get_object_ptr(name const & n) const {
        auto it = m_object_dictionary.find(n);
        if (it == m_object_dictionary.end()) {
            if (has_parent())
                return m_parent->get_object_ptr(n);
            else
                return nullptr;
        } else {
            return it->second;
        }
    }

    object const & get_object(name const & n) const {
        object const * ptr = get_object_ptr(n);
        if (ptr) {
            return *ptr;
        } else {
            std::ostringstream s;
            s << "unknown object '" << n << "'";
            throw exception (s.str());
        }
    }

    imp():
        m_num_children(0) {
        init_uvars();
    }

    explicit imp(std::shared_ptr<imp> const & parent):
        m_num_children(0),
        m_parent(parent) {
        m_parent->inc_children();
    }

    ~imp() {
        if (m_parent)
            m_parent->dec_children();
        std::for_each(m_objects.begin(), m_objects.end(), [](object * obj) { delete obj; });
    }
};

environment::environment():
    m_imp(new imp()) {
}

environment::environment(imp * new_ptr):
    m_imp(new_ptr) {
}

environment::environment(std::shared_ptr<imp> const & ptr):
    m_imp(ptr) {
}

environment::~environment() {
}

level environment::define_uvar(name const & n, level const & l) {
    return m_imp->define_uvar(n, l);
}

bool environment::is_ge(level const & l1, level const & l2) const {
    return m_imp->is_ge(l1, l2);
}

void environment::display_uvars(std::ostream & out) const {
    m_imp->display_uvars(out);
}

environment environment::mk_child() const {
    return environment(new imp(m_imp));
}

bool environment::has_children() const {
    return m_imp->has_children();
}

bool environment::has_parent() const {
    return m_imp->has_parent();
}

environment environment::parent() const {
    lean_assert(has_parent());
    return environment(m_imp->m_parent);
}

level environment::get_uvar(name const & n) const {
    return m_imp->get_uvar(n);
}

void environment::add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
    m_imp->check_no_children();
    m_imp->check_name(n);
    infer_universe(t, *this);
    expr v_t = infer_type(v, *this);
    if (!is_convertible(t, v_t, *this)) {
        std::ostringstream buffer;
        buffer << "type mismatch when defining '" << n << "'\n"
               << "expected type:\n" << t << "\n"
               << "given type:\n" << v_t;
        throw exception(buffer.str());
    }
    m_imp->add_definition(n, t, v, opaque);
}

void environment::add_definition(name const & n, expr const & v, bool opaque) {
    m_imp->check_no_children();
    m_imp->check_name(n);
    expr v_t = infer_type(v, *this);
    m_imp->add_definition(n, v_t, v, opaque);
}

void environment::add_fact(name const & n, expr const & t) {
    m_imp->check_no_children();
    m_imp->check_name(n);
    infer_universe(t, *this);
    m_imp->add_fact(n, t);
}

environment::object const & environment::get_object(name const & n) const {
    return m_imp->get_object(n);
}

environment::object const * environment::get_object_ptr(name const & n) const {
    return m_imp->get_object_ptr(n);
}
}
