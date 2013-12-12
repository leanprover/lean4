/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdlib>
#include <algorithm>
#include <vector>
#include <tuple>
#include <set>
#include <unordered_map>
#include "util/thread.h"
#include "util/safe_arith.h"
#include "util/realpath.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/threadsafe_environment.h"
#include "kernel/type_checker.h"
#include "kernel/normalizer.h"

namespace lean {
static name g_builtin_module("builtin_module");
class extension_factory {
    std::vector<environment::mk_extension> m_makers;
    mutex                                  m_makers_mutex;
public:
    unsigned register_extension(environment::mk_extension mk) {
        lock_guard<mutex> lock(m_makers_mutex);
        unsigned r = m_makers.size();
        m_makers.push_back(mk);
        return r;
    }

    std::unique_ptr<environment::extension> mk(unsigned extid) {
        lock_guard<mutex> lock(m_makers_mutex);
        return m_makers[extid]();
    }
};

static std::unique_ptr<extension_factory> g_extension_factory;
static extension_factory & get_extension_factory() {
    if (!g_extension_factory)
        g_extension_factory.reset(new extension_factory());
    return *g_extension_factory;
}

unsigned environment::register_extension(mk_extension mk) {
    return get_extension_factory().register_extension(mk);
}

/** \brief Implementation of the Lean environment. */
struct environment::imp {
    // Remark: only named objects are stored in the dictionary.
    typedef std::unordered_map<name, object, name_hash, name_eq> object_dictionary;
    typedef std::tuple<level, level, int> constraint;
    std::weak_ptr<imp>                   m_this;
    // Universe variable management
    std::vector<constraint>              m_constraints;
    std::vector<level>                   m_uvars;
    // Children environment management
    atomic<unsigned>                     m_num_children;
    std::shared_ptr<imp>                 m_parent;
    // Object management
    std::vector<object>                  m_objects;
    object_dictionary                    m_object_dictionary;
    std::unique_ptr<type_checker>        m_type_checker;
    std::set<name>                       m_imported_modules;   // set of imported files and builtin modules

    std::vector<std::unique_ptr<extension>> m_extensions;
    friend class extension;

    // This mutex is only used to implement threadsafe environment objects
    // in the external APIs
    shared_mutex                         m_mutex;

    environment env() const {
        lean_assert(!m_this.expired()); // it is not possible to expire since it is a reference to this object
        lean_assert(this == m_this.lock().get());
        return environment(m_this);
    }

    extension & get_extension_core(unsigned extid) {
        if (extid >= m_extensions.size())
            m_extensions.resize(extid+1);
        if (!m_extensions[extid]) {
            std::unique_ptr<extension> ext = get_extension_factory().mk(extid);
            ext->m_extid = extid;
            ext->m_env   = this;
            m_extensions[extid].swap(ext);
        }
        return *(m_extensions[extid].get());
    }

    unsigned get_max_weight(expr const & e) {
        unsigned w = 0;
        auto proc = [&](expr const & c, unsigned) {
            if (is_constant(c)) {
                optional<object> obj = get_object_core(const_name(c));
                if (obj)
                    w = std::max(w, obj->get_weight());
            }
            return true;
        };
        for_each_fn<decltype(proc)> visitor(proc);
        visitor(e);
        return w;
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
    void check_name_core(name const & n) {
        if (has_parent())
            m_parent->check_name_core(n);
        if (m_object_dictionary.find(n) != m_object_dictionary.end())
            throw already_declared_exception(env(), n);
    }

    void check_name(name const & n) {
        if (has_children())
            throw read_only_environment_exception(env());
        check_name_core(n);
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
    optional<object> get_object_core(name const & n) const {
        auto it = m_object_dictionary.find(n);
        if (it == m_object_dictionary.end()) {
            if (has_parent())
                return m_parent->get_object_core(n);
            else
                return none_object();
        } else {
            return some_object(it->second);
        }
    }

    object get_object(name const & n) const {
        optional<object> obj = get_object_core(n);
        if (obj) {
            return *obj;
        } else {
            throw unknown_object_exception(env(), n);
        }
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
            return k <= 0;
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
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    /** \brief Return true iff l1 >= l2 is implied by asserted universe constraints. */
    bool is_ge(level const & l1, level const & l2) {
        if (has_parent())
            return m_parent->is_ge(l1, l2);
        else
            return is_ge(l1, l2, 0);
    }

    /** \brief Add a new universe variable */
    level add_uvar(name const & n) {
        check_name(n);
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
                    to_add.emplace_back(u, l3, u_l3_d);
            }
        }
        m_constraints.emplace_back(u, v, d);
        for (constraint const & c : to_add) {
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
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    /** \brief Add a new universe variable with constraint n >= l */
    level add_uvar(name const & n, level const & l) {
        if (has_parent())
            throw kernel_exception(env(), "invalid universe declaration, universe variables can only be declared in top-level environments");
        if (has_children())
            throw read_only_environment_exception(env());
        level r = add_uvar(n);
        add_constraints(r, l, 0);
        register_named_object(mk_uvar_decl(n, l));
        return r;
    }

    /**
        \brief Return the universe variable with given name. Throw an
        exception if the environment and its ancestors do not
        contain a universe variable named \c n.
    */
    level get_uvar(name const & n) const {
        if (has_parent()) {
            return m_parent->get_uvar(n);
        } else {
            auto it = std::find_if(m_uvars.begin(), m_uvars.end(), [&](level const & l) { return uvar_name(l) == n; });
            if (it == m_uvars.end())
                throw unknown_universe_variable_exception(env(), n);
            else
                return *it;
        }
    }

    /**
       \brief Initialize the set of universe variables with bottom
    */
    void init_uvars() {
        m_uvars.emplace_back();
    }

    /**
       The kernel should *not* accept expressions containing cached types.
       Reason: Cached types may introduce unsoundness.
       For example, in the environment env, the constant x may have type T.
       Now suppose we are trying to add a new definition D that contains x,
       and x is associated with a cached type T'. The cached type may allow
       us to accept a definition that is type incorrect with respect to env.
    */
    void check_no_cached_type(expr const & e) {
        if (find(e, [](expr const & a) { return is_constant(a) && const_type(a); }))
            throw kernel_exception(env(), "expression has a constant with a cached type, this is a bug in one of Lean tactics and/or solvers");
    }

    /**
        \brief Throw an exception if \c t is not a type or type of \c
        v is not convertible to \c t.
    */
    void check_type(name const & n, expr const & t, expr const & v) {
        m_type_checker->check_type(t);
        expr v_t = m_type_checker->infer_type(v);
        if (!m_type_checker->is_convertible(v_t, t))
            throw def_type_mismatch_exception(env(), n, t, v, v_t);
    }

    /** \brief Throw exception if it is not a valid new definition */
    void check_new_definition(name const & n, expr const & t, expr const & v) {
        check_name(n);
        check_type(n, t, v);
    }

    /** \brief Add a new builtin value to this environment */
    void add_builtin(expr const & v) {
        if (!is_value(v))
            throw invalid_builtin_value_declaration(env(), v);
        name const & n = to_value(v).get_name();
        check_name(n);
        name const & u = to_value(v).get_unicode_name();
        check_name(u);
        register_named_object(mk_builtin(v));
        if (u != n) {
            add_definition(u, to_value(v).get_type(), mk_constant(n), false);
        }
    }

    /** \brief Add a new builtin value set to this environment */
    void add_builtin_set(expr const & r) {
        if (!is_value(r))
            throw invalid_builtin_value_declaration(env(), r);
        check_name(to_value(r).get_name());
        register_named_object(mk_builtin_set(r));
    }

    /** \brief Add new definition. */
    void add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
        check_no_cached_type(t);
        check_no_cached_type(v);
        check_new_definition(n, t, v);
        unsigned w = get_max_weight(v) + 1;
        register_named_object(mk_definition(n, t, v, opaque, w));
    }

    /**
        \brief Add new definition.
        The type of the new definition is the type of \c v.
    */
    void add_definition(name const & n, expr const & v, bool opaque) {
        check_no_cached_type(v);
        check_name(n);
        expr v_t = m_type_checker->infer_type(v);
        unsigned w = get_max_weight(v) + 1;
        register_named_object(mk_definition(n, v_t, v, opaque, w));
    }

    /** \brief Add new theorem. */
    void add_theorem(name const & n, expr const & t, expr const & v) {
        check_no_cached_type(t);
        check_no_cached_type(v);
        check_new_definition(n, t, v);
        register_named_object(mk_theorem(n, t, v));
    }

    /** \brief Add new axiom. */
    void add_axiom(name const & n, expr const & t) {
        check_no_cached_type(t);
        check_name(n);
        m_type_checker->check_type(t);
        register_named_object(mk_axiom(n, t));
    }

    /** \brief Add new variable. */
    void add_var(name const & n, expr const & t) {
        check_no_cached_type(t);
        check_name(n);
        m_type_checker->check_type(t);
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

    expr infer_type(expr const & e, context const & ctx) {
        return m_type_checker->infer_type(e, ctx);
    }

    expr normalize(expr const & e, context const & ctx) {
        return m_type_checker->get_normalizer()(e, ctx);
    }

    /** \brief Display universal variable constraints and objects stored in this environment and its parents. */
    void display(std::ostream & out) const {
        if (has_parent())
            m_parent->display(out);
        for (object const & obj : m_objects) {
            if (obj.has_name()) {
                out << obj.keyword() << " " << obj.get_name() << "\n";
            }
        }
    }

    bool already_imported(name const & n) const {
        if (m_imported_modules.find(n) != m_imported_modules.end())
            return true;
        else if (has_parent())
            return m_parent->already_imported(n);
        else
            return false;
    }

    bool mark_imported_core(name n) {
        if (already_imported(n)) {
            return false;
        } else if (has_children()) {
            throw read_only_environment_exception(env());
        } else {
            m_imported_modules.insert(n);
            return true;
        }
    }

    bool mark_imported(char const * fname) {
        return mark_imported_core(name(realpath(fname)));
    }

    bool mark_builtin_imported(char const * id) {
        return mark_imported_core(name(g_builtin_module, id));
    }

    imp():
        m_num_children(0) {
        init_uvars();
    }

    imp(std::shared_ptr<imp> const & parent):
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
    m_ptr(new imp()) {
    m_ptr->m_this = m_ptr;
    m_ptr->m_type_checker.reset(new type_checker(*this));
}

// used when creating a new child environment
environment::environment(std::shared_ptr<imp> const & parent, bool):
    m_ptr(new imp(parent)) {
    m_ptr->m_this = m_ptr;
    m_ptr->m_type_checker.reset(new type_checker(*this));
}

// used when creating a reference to the parent environment
environment::environment(std::shared_ptr<imp> const & ptr):
    m_ptr(ptr) {
}

environment::environment(weak_ref const & r) {
    if (r.expired())
        throw exception("weak reference to environment object has expired (i.e., the environment has been deleted)");
    m_ptr = r.lock();
}

environment::~environment() {
}

environment environment::mk_child() const {
    return environment(m_ptr, true);
}

bool environment::has_children() const {
    return m_ptr->has_children();
}

bool environment::has_parent() const {
    return m_ptr->has_parent();
}

environment environment::parent() const {
    lean_assert(has_parent());
    return environment(m_ptr->m_parent);
}

level environment::add_uvar(name const & n, level const & l) {
    return m_ptr->add_uvar(n, l);
}

bool environment::is_ge(level const & l1, level const & l2) const {
    return m_ptr->is_ge(l1, l2);
}

level environment::get_uvar(name const & n) const {
    return m_ptr->get_uvar(n);
}

void environment::add_builtin(expr const & v) {
    return m_ptr->add_builtin(v);
}

void environment::add_builtin_set(expr const & r) {
    return m_ptr->add_builtin_set(r);
}

void environment::add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
    m_ptr->add_definition(n, t, v, opaque);
}

void environment::add_theorem(name const & n, expr const & t, expr const & v) {
    m_ptr->add_theorem(n, t, v);
}

void environment::add_definition(name const & n, expr const & v, bool opaque) {
    m_ptr->add_definition(n, v, opaque);
}

void environment::add_axiom(name const & n, expr const & t) {
    m_ptr->add_axiom(n, t);
}

void environment::add_var(name const & n, expr const & t) {
    m_ptr->add_var(n, t);
}

void environment::add_neutral_object(neutral_object_cell * o) {
    m_ptr->m_objects.push_back(mk_neutral(o));
}

object environment::get_object(name const & n) const {
    return m_ptr->get_object(n);
}

optional<object> environment::find_object(name const & n) const {
    return m_ptr->get_object_core(n);
}

unsigned environment::get_num_objects(bool local) const {
    return m_ptr->get_num_objects(local);
}

object const & environment::get_object(unsigned i, bool local) const {
    return m_ptr->get_object(i, local);
}

expr environment::infer_type(expr const & e, context const & ctx) const {
    return m_ptr->infer_type(e, ctx);
}

expr environment::normalize(expr const & e, context const & ctx) const {
    return m_ptr->normalize(e, ctx);
}

void environment::display(std::ostream & out) const {
    m_ptr->display(out);
}

bool environment::mark_imported(char const * fname) {
    return m_ptr->mark_imported(fname);
}

bool environment::mark_builtin_imported(char const * id) {
    return m_ptr->mark_builtin_imported(id);
}

environment::extension const & environment::get_extension_core(unsigned extid) const {
    return m_ptr->get_extension_core(extid);
}

environment::extension & environment::get_extension_core(unsigned extid) {
    return m_ptr->get_extension_core(extid);
}

environment::extension::extension():
    m_env(nullptr),
    m_extid(0) {
}

environment::extension::~extension() {
}

environment::extension const * environment::extension::get_parent_core() const {
    if (m_env == nullptr)
        return nullptr;
    imp * parent = m_env->m_parent.get();
    while (parent) {
        if (m_extid < parent->m_extensions.size()) {
            extension * ext = parent->m_extensions[m_extid].get();
            if (ext)
                return ext;
        }
        parent = parent->m_parent.get();
    }
    return nullptr;
}

read_only_shared_environment::read_only_shared_environment(environment const & env):
    m_env(env),
    m_lock(m_env.m_ptr->m_mutex) {
}
read_only_shared_environment::~read_only_shared_environment() {}

read_write_shared_environment::read_write_shared_environment(environment const & env):
    m_env(env),
    m_lock(m_env.m_ptr->m_mutex) {
}
read_write_shared_environment::~read_write_shared_environment() {}
}
