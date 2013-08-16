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
#include "kernel_exception.h"
#include "environment.h"
#include "safe_arith.h"
#include "type_check.h"
#include "exception.h"
#include "debug.h"

namespace lean {

/** \brief Implementation of the Lean environment. */
struct environment::imp {
    // Remark: only named objects are stored in the dictionary.
    typedef std::unordered_map<name, object, name_hash, name_eq> object_dictionary;
    typedef std::tuple<level, level, int> constraint;
    // Universe variable management
    std::vector<constraint>              m_constraints;
    std::vector<level>                   m_uvars;
    // Children environment management
    std::atomic<unsigned>                m_num_children;
    std::shared_ptr<imp>                 m_parent;
    // Object management
    std::vector<object>                  m_objects;
    object_dictionary                    m_object_dictionary;
    // Expression formatter && locator
    std::shared_ptr<expr_formatter>      m_formatter;

    expr_formatter & get_formatter() {
        if (m_formatter) {
            return *m_formatter;
        } else {
            // root environments always have a formatter.
            lean_assert(has_parent());
            return m_parent->get_formatter();
        }
    }

    /**
       \brief Return true iff this environment has children.

       \remark If an environment has children than it cannot be
       updated. That is, it is read-only.
    */
    bool has_children() const { return m_num_children > 0; }
    void inc_children() { m_num_children++; }
    void dec_children() { m_num_children--; }

    /** \brief Return true iff this environment has a parent environment */
    bool has_parent() const { return m_parent != nullptr; }

    /** \brief Throw exception if environment or its ancestors already have an object with the given name. */
    void check_name_core(name const & n, environment const & env) {
        if (has_parent())
            m_parent->check_name_core(n, env);
        if (m_object_dictionary.find(n) != m_object_dictionary.end())
            throw already_declared_exception(env, n);
    }

    void check_name(name const & n, environment const & env) {
        if (has_children())
            throw read_only_environment_exception(env);
        check_name_core(n, env);
    }

    /** \brief Store new named object inside internal data-structures */
    void register_named_object(object const & new_obj) {
        m_objects.push_back(new_obj);
        m_object_dictionary.insert(std::make_pair(new_obj.get_name(), new_obj));
    }

    /**
        \brief Return the object named \c n in the environment or its
        ancestors. Return null object if there is no object with the
        given name.
    */
    object const & get_object_core(name const & n) const {
        auto it = m_object_dictionary.find(n);
        if (it == m_object_dictionary.end()) {
            if (has_parent())
                return m_parent->get_object_core(n);
            else
                return object::null();
        } else {
            return it->second;
        }
    }

    object const & get_object(name const & n, environment const & env) const {
        object const & obj = get_object_core(n);
        if (obj)
            return obj;
        else
            throw unknown_object_exception(env, n);
    }

    /**
        \brief Return true if u >= v + k is implied by constraints
        \pre is_uvar(u) && is_uvar(v)
    */
    bool is_implied(level const & u, level const & v, int k) {
        lean_assert(is_uvar(u) && is_uvar(v));
        if (u == v)
            return k <= 0;
        else
            return std::any_of(m_constraints.begin(), m_constraints.end(),
                               [&](constraint const & c) { return std::get<0>(c) == u && std::get<1>(c) == v && std::get<2>(c) >= k; });
    }

    /** \brief Return true iff l1 >= l2 + k by asserted universe constraints. */
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

    /** \brief Return true iff l1 >= l2 is implied by asserted universe constraints. */
    bool is_ge(level const & l1, level const & l2) {
        if (has_parent())
            return m_parent->is_ge(l1, l2);
        else
            return is_ge(l1, l2, 0);
    }

    /** \brief Add a new universe variable */
    level add_uvar(name const & n, environment const & env) {
        check_name(n, env);
        level r(n);
        m_uvars.push_back(r);
        return r;
    }

    /**
        \brief Add basic constraint u >= v + d, and all basic
        constraints implied by transitivity.

        \pre is_uvar(u) && is_uvar(v)
    */
    void add_constraint(level const & u, level const & v, int d) {
        lean_assert(is_uvar(u) && is_uvar(v));
        if (is_implied(u, v, d))
            return; // redundant
        buffer<constraint> to_add;
        for (constraint const & c : m_constraints) {
            if (std::get<0>(c) == v) {
                level const & l3 = std::get<1>(c);
                int u_l3_d = safe_add(d, std::get<2>(c));
                if (!is_implied(u, l3, u_l3_d))
                    to_add.push_back(constraint(u, l3, u_l3_d));
            }
        }
        m_constraints.push_back(constraint(u, v, d));
        for (constraint const & c: to_add) {
            m_constraints.push_back(c);
        }
    }

    /**
        \brief Add all basic constraints implied by n >= l + k

        A basic constraint is a constraint of the form u >= v + k
        where u and v are universe variables.
    */
    void add_constraints(level const & n, level const & l, int k) {
        lean_assert(is_uvar(n));
        switch (kind(l)) {
        case level_kind::UVar: add_constraint(n, l, k); return;
        case level_kind::Lift: add_constraints(n, lift_of(l), safe_add(k, lift_offset(l))); return;
        case level_kind::Max:  std::for_each(max_begin_levels(l), max_end_levels(l), [&](level const & l1) { add_constraints(n, l1, k); }); return;
        }
        lean_unreachable();
    }

    /** \brief Add a new universe variable with constraint n >= l */
    level add_uvar(name const & n, level const & l, environment const & env) {
        if (has_parent())
            throw kernel_exception(env, "invalid universe declaration, universe variables can only be declared in top-level environments");
        if (has_children())
            throw read_only_environment_exception(env);
        level r = add_uvar(n, env);
        add_constraints(r, l, 0);
        register_named_object(mk_uvar_decl(n, l));
        return r;
    }

    /**
        \brief Return the universe variable with given name. Throw an
        exception if the environment and its ancestors do not
        contain a universe variable named \c n.
    */
    level get_uvar(name const & n, environment const & env) const {
        if (has_parent()) {
            return m_parent->get_uvar(n, env);
        } else {
            auto it = std::find_if(m_uvars.begin(), m_uvars.end(), [&](level const & l) { return uvar_name(l) == n; });
            if (it == m_uvars.end())
                throw unknown_universe_variable_exception(env, n);
            else
                return *it;
        }
    }

    /**
       \brief Initialize the set of universe variables with bottom
    */
    void init_uvars() {
        m_uvars.push_back(level());
    }

    /**
        \brief Throw an exception if \c t is not a type or type of \c
        v is not convertible to \c t.

        \remark env is the smart pointer of imp. We need it because
        infer_universe and infer_type expect an environment instead of environment::imp.
    */
    void check_type(name const & n, expr const & t, expr const & v, environment const & env) {
        infer_universe(t, env);
        expr v_t = infer_type(v, env);
        if (!is_convertible(t, v_t, env))
            throw def_type_mismatch_exception(env, n, t, v, v_t);
    }

    /** \brief Throw exception if it is not a valid new definition */
    void check_new_definition(name const & n, expr const & t, expr const & v, environment const & env) {
        check_name(n, env);
        check_type(n, t, v, env);
    }

    /** \brief Add new definition. */
    void add_definition(name const & n, expr const & t, expr const & v, bool opaque, environment const & env) {
        check_new_definition(n, t, v, env);
        register_named_object(mk_definition(n, t, v, opaque));
    }

    /**
        \brief Add new definition.
        The type of the new definition is the type of \c v.
    */
    void add_definition(name const & n, expr const & v, bool opaque, environment const & env) {
        check_name(n, env);
        expr v_t = infer_type(v, env);
        register_named_object(mk_definition(n, v_t, v, opaque));
    }

    /** \brief Add new theorem. */
    void add_theorem(name const & n, expr const & t, expr const & v, environment const & env) {
        check_new_definition(n, t, v, env);
        register_named_object(mk_theorem(n, t, v));
    }

    /** \brief Add new axiom. */
    void add_axiom(name const & n, expr const & t, environment const & env) {
        check_name(n, env);
        infer_universe(t, env);
        register_named_object(mk_axiom(n, t));
    }

    /** \brief Add new variable. */
    void add_var(name const & n, expr const & t, environment const & env) {
        check_name(n, env);
        infer_universe(t, env);
        register_named_object(mk_var_decl(n, t));
    }

    unsigned get_num_objects(bool local) const {
        if (local || !has_parent()) {
            return m_objects.size();
        } else {
            return m_objects.size() + m_parent->get_num_objects(false);
        }
    }

    object const & get_object(unsigned i, bool local) const {
        if (local || !has_parent()) {
            return m_objects[i];
        } else {
            unsigned num_parent_objects = m_parent->get_num_objects(false);
            if (i >= num_parent_objects)
                return m_objects[i - num_parent_objects];
            else
                return m_parent->get_object(i, false);
        }
    }

    /** \brief Display universal variable constraints and objects stored in this environment and its parents. */
    void display(std::ostream & out, environment const & env) const {
        if (has_parent())
            m_parent->display(out, env);
        for (object const & obj : m_objects) {
            if (obj.has_name()) {
                out << obj.keyword() << " " << obj.get_name() << "\n";
            }
        }
    }

    imp():
        m_num_children(0) {
        init_uvars();
        m_formatter = mk_simple_expr_formatter();
    }

    explicit imp(std::shared_ptr<imp> const & parent):
        m_num_children(0),
        m_parent(parent) {
        m_parent->inc_children();
    }

    ~imp() {
        if (m_parent)
            m_parent->dec_children();
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

void environment::set_formatter(std::shared_ptr<expr_formatter> const & formatter) {
    lean_assert(formatter);
    m_imp->m_formatter = formatter;
}

expr_formatter & environment::get_formatter() const {
    return m_imp->get_formatter();
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

level environment::add_uvar(name const & n, level const & l) {
    return m_imp->add_uvar(n, l, *this);
}

bool environment::is_ge(level const & l1, level const & l2) const {
    return m_imp->is_ge(l1, l2);
}

level environment::get_uvar(name const & n) const {
    return m_imp->get_uvar(n, *this);
}

void environment::add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
    m_imp->add_definition(n, t, v, opaque, *this);
}

void environment::add_theorem(name const & n, expr const & t, expr const & v) {
    m_imp->add_theorem(n, t, v, *this);
}

void environment::add_definition(name const & n, expr const & v, bool opaque) {
    m_imp->add_definition(n, v, opaque, *this);
}

void environment::add_axiom(name const & n, expr const & t) {
    m_imp->add_axiom(n, t, *this);
}

void environment::add_var(name const & n, expr const & t) {
    m_imp->add_var(n, t, *this);
}

void environment::add_neutral_object(neutral_object_cell * o) {
    m_imp->m_objects.push_back(mk_neutral(o));
}

object const & environment::get_object(name const & n) const {
    return m_imp->get_object(n, *this);
}

unsigned environment::get_num_objects(bool local) const {
    return m_imp->get_num_objects(local);
}

object const & environment::get_object(unsigned i, bool local) const {
    return m_imp->get_object(i, local);
}

void environment::display(std::ostream & out) const {
    m_imp->display(out, *this);
}
}
