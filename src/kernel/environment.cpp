/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdlib>
#include <algorithm>
#include <vector>
#include <tuple>
#include <fstream>
#include <string>
#include <utility>
#include "util/thread.h"
#include "util/safe_arith.h"
#include "util/realpath.h"
#include "util/sstream.h"
#include "util/lean_path.h"
#include "util/flet.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/threadsafe_environment.h"
// #include "kernel/type_checker.h"
// #include "kernel/normalizer.h"
#include "version.h"

namespace lean {
class set_opaque_command : public neutral_object_cell {
    name m_obj_name;
    bool m_opaque;
public:
    set_opaque_command(name const & n, bool opaque):m_obj_name(n), m_opaque(opaque) {}
    virtual ~set_opaque_command() {}
    virtual char const * keyword() const { return "set_opaque"; }
    virtual void write(serializer & s) const { s << "Opa" << m_obj_name << m_opaque; }
    name const & get_obj_name() const { return m_obj_name; }
    bool get_flag() const { return m_opaque; }
};
static void read_set_opaque(environment const & env, io_state const &, deserializer & d) {
    name n = read_name(d);
    bool o = d.read_bool();
    env->set_opaque(n, o);
}
static object_cell::register_deserializer_fn set_opaque_ds("Opa", read_set_opaque);

bool is_set_opaque(object const & obj) {
    return dynamic_cast<set_opaque_command const *>(obj.cell());
}

name const & get_set_opaque_id(object const & obj) {
    lean_assert(is_set_opaque(obj));
    return static_cast<set_opaque_command const *>(obj.cell())->get_obj_name();
}

bool get_set_opaque_flag(object const & obj) {
    lean_assert(is_set_opaque(obj));
    return static_cast<set_opaque_command const *>(obj.cell())->get_flag();
}

class import_command : public neutral_object_cell {
    std::string m_mod_name;
public:
    import_command(std::string const & n):m_mod_name(n) {}
    virtual ~import_command() {}
    virtual char const * keyword() const { return "import"; }
    virtual void write(serializer & s) const { s << "import" << m_mod_name; }
    std::string const & get_module() const { return m_mod_name; }
};
static void read_import(environment const & env, io_state const & ios, deserializer & d) {
    std::string n = d.read_string();
    env->import(n, ios);
}
static object_cell::register_deserializer_fn import_ds("import", read_import);

class end_import_mark : public neutral_object_cell {
public:
    end_import_mark() {}
    virtual ~end_import_mark() {}
    virtual char const * keyword() const { return "EndImport"; }
    virtual void write(serializer &) const {}
};

// For Importing builtin modules
class begin_import_mark : public neutral_object_cell {
public:
    begin_import_mark() {}
    virtual ~begin_import_mark() {}
    virtual char const * keyword() const { return "BeginImport"; }
    virtual void write(serializer &) const {}
};

bool is_begin_import(object const & obj) {
    return dynamic_cast<import_command const*>(obj.cell());
}

optional<std::string> get_imported_module(object const & obj) {
    if (is_begin_import(obj)) {
        return optional<std::string>(static_cast<import_command const*>(obj.cell())->get_module());
    } else {
        return optional<std::string>();
    }
}

bool is_begin_builtin_import(object const & obj) {
    return dynamic_cast<begin_import_mark const*>(obj.cell());
}

bool is_end_import(object const & obj) {
    return dynamic_cast<end_import_mark const*>(obj.cell());
}

class extension_factory {
    std::vector<environment_cell::mk_extension> m_makers;
    mutex                                       m_makers_mutex;
public:
    unsigned register_extension(environment_cell::mk_extension mk) {
        lock_guard<mutex> lock(m_makers_mutex);
        unsigned r = m_makers.size();
        m_makers.push_back(mk);
        return r;
    }

    std::unique_ptr<environment_extension> mk(unsigned extid) {
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

unsigned environment_cell::register_extension(mk_extension mk) {
    return get_extension_factory().register_extension(mk);
}

environment environment_cell::env() const {
    lean_assert(!m_this.expired()); // it is not possible to expire since it is a reference to this object
    lean_assert(this == m_this.lock().get());
    return environment(m_this.lock());
}

environment environment_cell::parent() const {
    lean_assert(has_parent());
    return environment(m_parent);
}

environment environment_cell::mk_child() const {
    return environment(m_this.lock(), true);
}

environment_extension & environment_cell::get_extension_core(unsigned extid) {
    if (extid >= m_extensions.size())
        m_extensions.resize(extid+1);
    if (!m_extensions[extid]) {
        std::unique_ptr<environment_extension> ext = get_extension_factory().mk(extid);
        ext->m_extid = extid;
        ext->m_env   = this;
        m_extensions[extid].swap(ext);
    }
    return *(m_extensions[extid].get());
}

environment_extension const & environment_cell::get_extension_core(unsigned extid) const {
    return const_cast<environment_cell *>(this)->get_extension_core(extid);
}

unsigned environment_cell::get_max_weight(expr const & e) {
    unsigned w = 0;
    auto proc = [&](expr const & c, unsigned) {
        if (is_constant(c)) {
            optional<object> obj = get_object_core(const_name(c));
            if (obj)
                w = std::max(w, obj->get_weight());
        }
        return true;
        };
    for_each_fn visitor(proc);
    visitor(e);
    return w;
}

/** \brief Throw exception if environment or its ancestors already have an object with the given name. */
void environment_cell::check_name_core(name const & n) {
    if (has_parent())
        m_parent->check_name_core(n);
    if (m_object_dictionary.find(n) != m_object_dictionary.end())
        throw_already_declared(env(), n);
}

void environment_cell::check_name(name const & n) {
    if (has_children())
        throw_read_only_environment(env());
    check_name_core(n);
}

/** \brief Store new named object inside internal data-structures */
void environment_cell::register_named_object(object const & new_obj) {
    m_objects.push_back(new_obj);
    m_object_dictionary.insert(std::make_pair(new_obj.get_name(), new_obj));
}

/**
   \brief Return the object named \c n in the environment or its
   ancestors. Return null object if there is no object with the
   given name.
*/
optional<object> environment_cell::get_object_core(name const & n) const {
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

object environment_cell::get_object(name const & n) const {
    optional<object> obj = get_object_core(n);
    if (obj) {
        return *obj;
    } else {
        throw_unknown_object(env(), n);
    }
}

/**
   The kernel should *not* accept expressions containing Local or Meta.
   Reason: they may introduce unsoundness.
*/
void environment_cell::check_no_mlocal(expr const & e) {
    if (find(e, [](expr const & a, unsigned) { return is_mlocal(a); }))
        throw_kernel_exception(env(), "expression has metavariable and/or local constants, this is a bug in one of Lean tactics and/or solvers"); // LCOV_EXCL_LINE
}

/**
   \brief Throw an exception if \c t is not a type or type of \c
   v is not convertible to \c t.
*/
void environment_cell::check_type(name const & n, expr const & t, expr const & v) {
#if 0
    if (m_type_check) {
        m_type_checker->check_type(t);
        expr v_t = m_type_checker->check(v);
        if (!m_type_checker->is_convertible(v_t, t))
            throw def_type_mismatch_exception(env(), n, t, v, v_t);
    }
#endif
}

void environment_cell::check_type(expr const & t) {
#if 0
    if (m_type_check)
        m_type_checker->check_type(t);
#endif
}

/** \brief Throw exception if it is not a valid new definition */
void environment_cell::check_new_definition(name const & n, expr const & t, expr const & v) {
    check_name(n);
    check_type(n, t, v);
}

/** \brief Add new definition. */
void environment_cell::add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
    check_no_mlocal(t);
    check_no_mlocal(v);
    check_new_definition(n, t, v);
    unsigned w = get_max_weight(v) + 1;
    register_named_object(mk_definition(n, t, v, w));
    if (opaque)
        set_opaque(n, opaque);
}

/**
   \brief Add new definition.
   The type of the new definition is the type of \c v.
*/
void environment_cell::add_definition(name const & n, expr const & v, bool opaque) {
    check_no_mlocal(v);
    check_name(n);
    expr v_t;
#if 0
    if (m_type_check)
        v_t = m_type_checker->check(v);
    else
        v_t = m_type_checker->infer_type(v);
#endif
    unsigned w = get_max_weight(v) + 1;
    register_named_object(mk_definition(n, v_t, v, w));
    if (opaque)
        set_opaque(n, opaque);
}

/** \brief Add new theorem. */
void environment_cell::add_theorem(name const & n, expr const & t, expr const & v) {
    check_no_mlocal(t);
    check_no_mlocal(v);
    check_new_definition(n, t, v);
    register_named_object(mk_theorem(n, t, v));
}

void environment_cell::set_opaque(name const & n, bool opaque) {
    auto obj = find_object(n);
    if (!obj || !obj->is_definition())
        throw_kernel_exception(env(), sstream() << "set_opaque failed, '" << n << "' is not a definition");
    obj->set_opaque(opaque);
    add_neutral_object(new set_opaque_command(n, opaque));
}

/** \brief Add new axiom. */
void environment_cell::add_axiom(name const & n, expr const & t) {
    check_no_mlocal(t);
    check_name(n);
    check_type(t);
    register_named_object(mk_axiom(n, t));
}

/** \brief Add new variable. */
void environment_cell::add_var(name const & n, expr const & t) {
    check_no_mlocal(t);
    check_name(n);
    check_type(t);
    register_named_object(mk_var_decl(n, t));
}

void environment_cell::add_neutral_object(neutral_object_cell * o) {
    m_objects.push_back(mk_neutral(o));
}

unsigned environment_cell::get_num_objects(bool local) const {
    if (local || !has_parent()) {
        return m_objects.size();
    } else {
        return m_objects.size() + m_parent->get_num_objects(false);
    }
}

object const & environment_cell::get_object(unsigned i, bool local) const {
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

expr environment_cell::type_check(expr const & e) const {
#if 0
    return m_type_checker->check(e, ctx);
#else
    return e;
#endif
}

expr environment_cell::infer_type(expr const & e) const {
#if 0
    return m_type_checker->infer_type(e, ctx);
#else
    return e;
#endif
}

expr environment_cell::normalize(expr const & e) const {
#if 0
    return m_type_checker->get_normalizer()(e, ctx, unfold_opaque);
#else
    return e;
#endif
}

bool environment_cell::is_proposition(expr const & e) const {
#if 0
    return m_type_checker->is_proposition(e, ctx);
#else
    return false;
#endif
}

bool environment_cell::already_imported(name const & n) const {
    if (m_imported_modules.find(n) != m_imported_modules.end())
        return true;
    else if (has_parent())
        return m_parent->already_imported(n);
    else
        return false;
}

bool environment_cell::mark_imported_core(name n) {
    if (already_imported(n)) {
        return false;
    } else if (has_children()) {
        throw_read_only_environment(env());
    } else {
        m_imported_modules.insert(n);
        return true;
    }
}

bool environment_cell::mark_imported(char const * fname) {
    return mark_imported_core(name(realpath(fname)));
}

void environment_cell::auxiliary_section(std::function<void()> fn) {
    add_neutral_object(new begin_import_mark());
    try {
        fn();
        add_neutral_object(new end_import_mark());
    } catch (...) {
        add_neutral_object(new end_import_mark());
        throw;
    }
}

void environment_cell::set_trusted_imported(bool flag) {
    m_trust_imported = flag;
}

static char const * g_olean_header   = "oleanfile";
static char const * g_olean_end_file = "EndFile";
void environment_cell::export_objects(std::string const & fname) {
    std::ofstream out(fname, std::ofstream::binary);
    serializer s(out);
    s << g_olean_header << LEAN_VERSION_MAJOR << LEAN_VERSION_MINOR;
    auto it  = begin_objects();
    auto end = end_objects();
    unsigned num_imports = 0;
    for (; it != end; ++it) {
        object const & obj = *it;
        if (dynamic_cast<import_command const*>(obj.cell())) {
            if (num_imports == 0)
                obj.write(s);
            num_imports++;
        } else if (dynamic_cast<end_import_mark const*>(obj.cell())) {
            lean_assert(num_imports > 0);
            num_imports--;
        } else if (dynamic_cast<begin_import_mark const*>(obj.cell())) {
            num_imports++;
        } else if (num_imports == 0) {
            obj.write(s);
        }
    }
    s << g_olean_end_file;
}

bool environment_cell::load_core(std::string const & fname, io_state const & ios, optional<std::string> const & mod_name) {
    if (!mod_name || mark_imported_core(fname)) {
        std::ifstream in(fname, std::ifstream::binary);
        if (!in.good())
            throw_kernel_exception(env(), sstream() << "failed to open file '" << fname << "'");
        deserializer d(in);
        std::string header;
        d >> header;
        if (header != g_olean_header)
            throw_kernel_exception(env(), sstream() << "file '" << fname << "' does not seem to be a valid object Lean file");
        unsigned major, minor;
        // Perhaps we should enforce the right version number
        d >> major >> minor;
        try {
            if (mod_name)
                add_neutral_object(new import_command(*mod_name));
            while (true) {
                std::string k;
                d >> k;
                if (k == g_olean_end_file) {
                    if (mod_name)
                        add_neutral_object(new end_import_mark());
                    return true;
                }
                read_object(env(), ios, k, d);
            }
        } catch (...) {
            if (mod_name)
                add_neutral_object(new end_import_mark());
            throw;
        }
    } else {
        return false;
    }
}

bool environment_cell::import(std::string const & fname, io_state const & ios) {
    flet<bool> set(m_type_check, !m_trust_imported);
    return load_core(realpath(find_file(fname, {".olean"}).c_str()), ios, optional<std::string>(fname));
}

void environment_cell::load(std::string const & fname, io_state const & ios) {
    load_core(fname, ios, optional<std::string>());
}

bool environment_cell::imported(std::string const & n) const {
    try {
        return already_imported(name(realpath(find_file(n, {".olean"}).c_str())));
    } catch (...) {
        // module named n does not even exist
        return false;
    }
}

environment_cell::environment_cell():
    m_num_children(0) {
    m_trust_imported = false;
    m_type_check     = true;
}

environment_cell::environment_cell(std::shared_ptr<environment_cell> const & parent):
    m_num_children(0),
    m_parent(parent) {
    m_trust_imported = false;
    m_type_check     = true;
    parent->inc_children();
}

environment_cell::~environment_cell() {
    if (m_parent)
        m_parent->dec_children();
}

environment::environment():
    m_ptr(std::make_shared<environment_cell>()) {
    m_ptr->m_this = m_ptr;
#if 0
    m_ptr->m_type_checker.reset(new type_checker(*this));
#endif
}

// used when creating a new child environment
environment::environment(std::shared_ptr<environment_cell> const & parent, bool):
    m_ptr(std::make_shared<environment_cell>(parent)) {
    m_ptr->m_this = m_ptr;
#if 0
    m_ptr->m_type_checker.reset(new type_checker(*this));
#endif
}

// used when creating a reference to the parent environment
environment::environment(std::shared_ptr<environment_cell> const & ptr):
    m_ptr(ptr) {
}

ro_environment::ro_environment(environment const & env):
    m_ptr(env.m_ptr) {
}

ro_environment::ro_environment(weak_ref const & r) {
    if (r.expired())
        throw_kernel_exception(*this, "weak reference to environment object has expired (i.e., the environment has been deleted)");
    m_ptr = r.lock();
}

environment_extension::environment_extension():
    m_env(nullptr),
    m_extid(0) {
}

environment_extension::~environment_extension() {
}

environment_extension const * environment_extension::get_parent_core() const {
    if (m_env == nullptr)
        return nullptr;
    environment_cell * parent = m_env->m_parent.get();
    while (parent) {
        if (m_extid < parent->m_extensions.size()) {
            environment_extension * ext = parent->m_extensions[m_extid].get();
            if (ext)
                return ext;
        }
        parent = parent->m_parent.get();
    }
    return nullptr;
}

read_only_shared_environment::read_only_shared_environment(ro_environment const & env):
    m_env(env),
    m_lock(const_cast<environment_cell*>(m_env.m_ptr.get())->m_mutex) {
}
read_only_shared_environment::~read_only_shared_environment() {}

read_write_shared_environment::read_write_shared_environment(environment const & env):
    m_env(env),
    m_lock(m_env.m_ptr->m_mutex) {
}
read_write_shared_environment::~read_write_shared_environment() {}
}
