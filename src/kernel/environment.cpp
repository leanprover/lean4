/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include <atomic>
#include <sstream>
#include <unordered_map>
#include "environment.h"
#include "safe_arith.h"
#include "type_check.h"
#include "exception.h"
#include "pp.h"
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

void environment::definition::display(std::ostream & out) const {
    out << header() << " " << m_name << " : " << m_type << " := " << m_value << "\n";
}

format pp_object_kind(char const * n) { return highlight(format(n), format::format_color::BLUE); }
constexpr unsigned indentation = 2; // TODO: must be option

format environment::definition::pp(environment const & env) const {
    return nest(indentation,
                  format{pp_object_kind(header()), format(" "), format(m_name), format(" : "), ::lean::pp(m_type, env), format(" :="),
                          line(), ::lean::pp(m_value), format(".")});
}

environment::fact::fact(name const & n, expr const & t):
    m_name(n),
    m_type(t) {
}

environment::fact::~fact() {
}

format environment::fact::pp(environment const & env) const {
    return nest(indentation,
                format{pp_object_kind(header()), format(" "), format(m_name), format(" : "), ::lean::pp(m_type, env), format(".")});
}

void environment::fact::display(std::ostream & out) const {
    out << header() << " " << m_name << " : " << m_type << "\n";
}

/** \brief Implementation of the Lean environment. */
struct environment::imp {
    typedef std::unordered_map<name, object *, name_hash, name_eq> object_dictionary;
    typedef std::tuple<level, level, int> constraint;
    // Universe variable management
    std::vector<constraint>              m_constraints;
    std::vector<level>                   m_uvars;
    // Children environment management
    std::atomic<unsigned>                m_num_children;
    std::shared_ptr<imp>                 m_parent;
    // Object management
    std::vector<object*>                 m_objects;
    object_dictionary                    m_object_dictionary;

    bool has_children() const { return m_num_children > 0; }
    void inc_children() { m_num_children++; }
    void dec_children() { m_num_children--; }

    bool has_parent() const { return m_parent != nullptr; }

    /** \brief Return true if l1 >= l2 + k is implied by constraints
        \pre is_uvar(l1) && is_uvar(l2)
     */
    bool is_implied(level const & l1, level const & l2, int k) {
        lean_assert(is_uvar(l1) && is_uvar(l2));
        if (l1 == l2)
            return k <= 0;
        else
            return std::any_of(m_constraints.begin(), m_constraints.end(),
                               [&](constraint const & c) { return std::get<0>(c) == l1 && std::get<1>(c) == l2 && std::get<2>(c) >= k; });
    }

    /** \brief Return true iff l1 >= l2 + k */
    bool is_ge(level const & l1, level const & l2, int k) {
        if (l1 == l2)
            return k == 0;
        switch (kind(l2)) {
        case level_kind::UVar:
            switch (kind(l1)) {
            case level_kind::UVar: return is_implied(l1, l2, k);
            case level_kind::Lift: return is_ge(lift_of(l1), l2, safe_sub(k, lift_offset(l1)));
            case level_kind::Max:  return std::any_of(max_begin_levels(l1), max_end_levels(l1), [&](level const & l) { return is_ge(l, l2, k); });
            }
        case level_kind::Lift: return is_ge(l1, lift_of(l2), safe_add(k, lift_offset(l2)));
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
        level r(n);
        m_uvars.push_back(r);
        return r;
    }

    void add_constraint(level const & l1, level const & l2, int d) {
        if (is_implied(l1, l2, d))
            return; // redundant
        buffer<constraint> to_add;
        for (constraint const & c : m_constraints) {
            if (std::get<0>(c) == l2) {
                level const & l3 = std::get<1>(c);
                int l1_l3_d = safe_add(d, std::get<2>(c));
                if (!is_implied(l1, l3, l1_l3_d))
                    to_add.push_back(constraint(l1, l3, l1_l3_d));
            }
        }
        m_constraints.push_back(constraint(l1, l2, d));
        for (constraint const & c: to_add) {
            m_constraints.push_back(c);
        }
    }

    void add_constraints(level const & n, level const & l, int k) {
        lean_assert(is_uvar(n));
        switch (kind(l)) {
        case level_kind::UVar: add_constraint(n, l, k); return;
        case level_kind::Lift: add_constraints(n, lift_of(l), safe_add(k, lift_offset(l))); return;
        case level_kind::Max:  std::for_each(max_begin_levels(l), max_end_levels(l), [&](level const & l1) { add_constraints(n, l1, k); }); return;
        }
        lean_unreachable();
    }

    level define_uvar(name const & n, level const & l) {
        if (has_parent())
            throw exception("invalid universe declaration, universe variables can only be declared in top-level environments");
        if (has_children())
            throw exception("invalid universe declaration, environment has children environments");
        level r = add_var(n);
        add_constraints(r, l, 0);
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
    }

    void display_uvars(std::ostream & out) const {
        for (constraint const & c : m_constraints) {
            out << uvar_name(std::get<0>(c)) << " >= " << uvar_name(std::get<1>(c));
            if (std::get<2>(c) >= 0)
                out << " + " << std::get<2>(c);
            out << "\n";
        }
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

    void check_add(name const & n) {
        check_no_children();
        check_name(n);
    }

    void add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
        m_objects.push_back(new definition(n, t, v, opaque));
        m_object_dictionary.insert(std::make_pair(n, m_objects.back()));
    }

    void add_theorem(name const & n, expr const & t, expr const & v) {
        m_objects.push_back(new theorem(n, t, v));
        m_object_dictionary.insert(std::make_pair(n, m_objects.back()));
    }

    void add_axiom(name const & n, expr const & t) {
        m_objects.push_back(new axiom(n, t));
        m_object_dictionary.insert(std::make_pair(n, m_objects.back()));
    }

    void add_var(name const & n, expr const & t) {
        m_objects.push_back(new variable(n, t));
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

    void display_objects(std::ostream & out, environment const & env) const {
        for (object const * obj : m_objects) {
            out << obj->pp(env) << "\n";
        }
    }

    /** \brief Display universal variable constraints and objects stored in this environment and its parents. */
    void display(std::ostream & out, environment const & env) const {
        if (has_parent())
            m_parent->display(out, env);
        display_uvars(out);
        display_objects(out, env);
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

void environment::check_type(name const & n, expr const & t, expr const & v) {
    infer_universe(t, *this);
    expr v_t = infer_type(v, *this);
    if (!is_convertible(t, v_t, *this)) {
        std::ostringstream buffer;
        buffer << "type mismatch when defining '" << n << "'\n"
               << "expected type:\n" << t << "\n"
               << "given type:\n" << v_t;
        throw exception(buffer.str());
    }
}

void environment::add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
    m_imp->check_no_children();
    m_imp->check_name(n);
    check_type(n, t, v);
    m_imp->add_definition(n, t, v, opaque);
}

void environment::add_theorem(name const & n, expr const & t, expr const & v) {
    m_imp->check_no_children();
    m_imp->check_name(n);
    check_type(n, t, v);
    m_imp->add_theorem(n, t, v);
}

void environment::add_definition(name const & n, expr const & v, bool opaque) {
    m_imp->check_add(n);
    expr v_t = infer_type(v, *this);
    m_imp->add_definition(n, v_t, v, opaque);
}

void environment::add_axiom(name const & n, expr const & t) {
    m_imp->check_add(n);
    infer_universe(t, *this);
    m_imp->add_axiom(n, t);
}

void environment::add_var(name const & n, expr const & t) {
    m_imp->check_add(n);
    infer_universe(t, *this);
    m_imp->add_var(n, t);
}

environment::object const & environment::get_object(name const & n) const {
    return m_imp->get_object(n);
}

environment::object const * environment::get_object_ptr(name const & n) const {
    return m_imp->get_object_ptr(n);
}

unsigned environment::get_num_objects() const {
    return m_imp->m_objects.size();
}

environment::object const & environment::get_object(unsigned i) const {
    return *(m_imp->m_objects[i]);
}

void environment::display_objects(std::ostream & out) const {
    m_imp->display_objects(out, *this);
}

void environment::display(std::ostream & out) const {
    m_imp->display(out, *this);
}
}
