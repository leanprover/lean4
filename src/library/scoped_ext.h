/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/list.h"
#include "util/rb_map.h"
#include "util/name.h"
#include "util/lua.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/module.h"
#include "library/fingerprint.h"

namespace lean {
enum class scope_kind { Namespace, Section };
typedef environment (*using_namespace_fn)(environment const &, io_state const &, name const &);
typedef environment (*export_namespace_fn)(environment const &, io_state const &, name const &);
typedef environment (*push_scope_fn)(environment const &, io_state const &, scope_kind);
typedef environment (*pop_scope_fn)(environment const &, io_state const &, scope_kind);

void register_scoped_ext(name const & n, using_namespace_fn use, export_namespace_fn ex, push_scope_fn push, pop_scope_fn pop);
/** \brief Use objects defined in the namespace \c n.
    If \c metaclasses is not empty, then only objects in the given "metaclasses" \c c are considered. */
environment using_namespace(environment const & env, io_state const & ios, name const & n, buffer<name> const & metaclasses);
environment using_namespace(environment const & env, io_state const & ios, name const & n);
/** \brief Export objects defined in the namespace \c n to current namespace.
    If \c metaclasses is not empty, then only objects in the given "metaclasses" \c c are considered. */
environment export_namespace(environment const & env, io_state const & ios, name const & n, buffer<name> const & metaclasses);
environment export_namespace(environment const & env, io_state const & ios, name const & n);

/** \brief Create a new scope, all scoped extensions are notified. */
environment push_scope(environment const & env, io_state const & ios, scope_kind k, name const & n = name());
/** \brief Delete the most recent scope, all scoped extensions are notified.
    \remark method throws an exception if there are no open scopes, or \c n does not match the name of the open scope
*/
environment pop_scope(environment const & env, io_state const & ios, name const & n = name());
/** \brief Similar to \c pop_scope, but it always succeed.
    It always pops the current open scope, and does nothing if there are no open scope.
*/
environment pop_scope_core(environment const & env, io_state const & ios);
/** \brief Return true iff there are open scopes */
bool has_open_scopes(environment const & env);

/** \brief Store in \c r all metaobject classes available in Lean */
void get_metaclasses(buffer<name> & r);

/** \brief Return true iff \c n is the name of a metaobject class available in Lean */
bool is_metaclass(name const & n);

/** \brief Add a new namespace (if it does not exist) */
environment add_namespace(environment const & env, name const & ns);

name const & get_namespace(environment const & env);
/** \brief Return the current stack of namespaces.
    Example: at
      namespace foo
      namespace bla
      namespace boo
      - It returns [foo.bla.boo, foo.bla, foo]

    \remark This is *not* the set of opened namespaces. */
list<name> const & get_namespaces(environment const & env);
bool in_section(environment const & env);

/** \brief Check if \c n may be a reference to a namespace, if it is return it.
    The procedure checks if \c n is a registered namespace, if it is not, it tries
    to prefix \c n with each prefix in the current scope. Example: suppose the scope is:
       namespace foo
         namespace bla
           namespace boo
              ...
    Then, the procedure tries n, 'foo.bla.boo'+n, 'foo.bla'+n, 'foo'+n. */
optional<name> to_valid_namespace_name(environment const & env, name const & n);

void open_scoped_ext(lua_State * L);

/** \brief Auxilary template used to simplify the creation of environment extensions that support
    the scope */
template<typename Config>
class scoped_ext : public environment_extension {
    typedef typename Config::state            state;
    typedef typename Config::entry            entry;
    static void add_entry(environment const & env, io_state const & ios, state & s, entry const & e) {
        Config::add_entry(env, ios, s, e);
    }
    static void  write_entry(serializer & s, entry const & e) { Config::write_entry(s, e); }
    static entry read_entry(deserializer & d) { return Config::read_entry(d); }
    static name const & get_class_name()  { return Config::get_class_name(); }
    static std::string const & get_serialization_key() { return Config::get_serialization_key(); }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return Config::get_fingerprint(e);
    }

    /* Current state */
    state                 m_state;
    /* Stack of states, it is updated using push/pop operations */
    list<state>           m_scopes;
    /* Nonlocal entries per scope (for sections).
       The nonlocal attributes declared in a section are not discarded when we close the section.
       So, we keep a stack of the nonlocal entries associated with these attributes.
       We re-add/declare them whenever a section is closed. */
    list<list<entry>>     m_nonlocal_entries;
    /* Mapping namespace -> entries for this namespace */
    name_map<list<entry>> m_entries_map;

    /* Update curret state with the entries from namespace \c n */
    void using_namespace_core(environment const & env, io_state const & ios, name const & n) {
        if (auto it = m_entries_map.find(n)) {
            buffer<entry> entries;
            to_buffer(*it, entries);
            unsigned i = entries.size();
            while (i > 0) {
                --i;
                add_entry(env, ios, m_state, entries[i]);
            }
        }
    }

    /* Add entry \c e to namespace \c n */
    void register_entry_core(name n, entry const & e) {
        if (auto it = m_entries_map.find(n))
            m_entries_map.insert(n, cons(e, *it));
        else
            m_entries_map.insert(n, to_list(e));
    }

    /* Add entry \c e to namespace \c n. If \c n is the anonymous/root
       namespace, then update current state with this entry.
       This method is invoked when importing files. */
    scoped_ext _register_entry(environment const & env, io_state const & ios, name n, entry const & e) const {
        lean_assert(get_namespace(env).is_anonymous());
        scoped_ext r(*this);
        r.register_entry_core(n, e);
        if (n.is_anonymous())
            add_entry(env, ios, r.m_state, e);
        return r;
    }

    /* Add a nonlocal entry. Register it in the current namespace, mark it as nonlocal, and
       update current state */
    scoped_ext _add_entry(environment const & env, io_state const & ios, entry const & e) const {
        scoped_ext r(*this);
        r.register_entry_core(get_namespace(env), e);
        if (r.m_nonlocal_entries)
            r.m_nonlocal_entries = cons(cons(e, head(r.m_nonlocal_entries)), tail(r.m_nonlocal_entries));
        add_entry(env, ios, r.m_state, e);
        return r;
    }

    /* Add entry to current state */
    scoped_ext _add_tmp_entry(environment const & env, io_state const & ios, entry const & e) const {
        scoped_ext r(*this);
        add_entry(env, ios, r.m_state, e);
        return r;
    }

    /* Add \c e to the first \c n states in \c l.
       \pre length(l) >= n */
    static list<state> add_first_n(environment const & env, io_state const & ios, list<state> const & l, entry const & e, unsigned n) {
        if (n == 0) {
            return l;
        } else {
            state new_s = head(l);
            add_entry(env, ios, new_s, e);
            return cons(new_s, add_first_n(env, ios, tail(l), e, n-1));
        }
    }

    scoped_ext _add_entry_at(environment const & env, io_state const & ios, entry const & e, name const & ns) const {
        lean_assert(get_namespace(env) != ns);
        scoped_ext r(*this);
        r.register_entry_core(ns, e);
        unsigned n     = 0;
        bool     found = false;
        lean_assert(length(m_scopes) == length(get_namespaces(env)));
        if (ns.is_anonymous()) {
            found = true;
            n     = length(m_scopes);
        } else {
            for (name const & ns2 : get_namespaces(env)) {
                if (ns == ns2) {
                    found = true;
                    break;
                }
                n++;
            }
        }
        if (found) {
            // must update m_nonlocal_entries
            r.m_scopes = add_first_n(env, ios, r.m_scopes, e, n);
            add_entry(env, ios, r.m_state, e);
        }
        return r;
    }

public:
    /** \brief Return an updated state with the entries from namespace \c n. */
    scoped_ext using_namespace(environment const & env, io_state const & ios, name const & n) const {
        scoped_ext r(*this);
        r.using_namespace_core(env, ios, n);
        return r;
    }

    /** \brief Copy entries from the given namespace to the current namespace. */
    environment export_namespace(environment env, io_state const & ios, name const & ns) const {
        if (auto it = m_entries_map.find(ns)) {
            buffer<entry> entries;
            to_buffer(*it, entries);
            unsigned i      = entries.size();
            name current_ns = get_namespace(env);
            while (i > 0) {
                --i;
                env = add_entry(env, ios, entries[i], current_ns, true);
            }
        }
        return env;
    }

    /** \brief Open a namespace/section. It return the new updated state. */
    scoped_ext push() const {
        scoped_ext r(*this);
        r.m_scopes           = cons(m_state, r.m_scopes);
        r.m_nonlocal_entries = cons(list<entry>(), r.m_nonlocal_entries);
        return r;
    }

    /** \brief Close namespace/section. It returns the new updated
        state, and a list of entries that must be re-added/declared.
        \pre There are open namespaces */
    pair<scoped_ext, list<entry>> pop(scope_kind k) const {
        lean_assert(!is_nil(m_scopes));
        scoped_ext r(*this);
        r.m_state  = head(m_scopes);
        r.m_scopes = tail(m_scopes);
        if (k == scope_kind::Section) {
            auto entries = head(r.m_nonlocal_entries);
            r.m_nonlocal_entries = tail(r.m_nonlocal_entries);
            if (r.m_nonlocal_entries)
                r.m_nonlocal_entries = cons(append(entries, head(r.m_nonlocal_entries)), tail(r.m_nonlocal_entries));
            return mk_pair(r, entries);
        } else {
            r.m_nonlocal_entries = tail(r.m_nonlocal_entries);
            return mk_pair(r, list<entry>());
        }
    }

    struct reg {
        unsigned m_ext_id;
        reg() {
            register_scoped_ext(get_class_name(), using_namespace_fn, export_namespace_fn, push_fn, pop_fn);
            register_module_object_reader(get_serialization_key(), reader);
            m_ext_id = environment::register_extension(std::make_shared<scoped_ext>());
        }
    };

    static reg * g_ext;
    static void initialize() { g_ext = new reg(); }
    static void finalize() { delete g_ext; }

    static scoped_ext const & get(environment const & env) {
        return static_cast<scoped_ext const &>(env.get_extension(g_ext->m_ext_id));
    }
    static environment update(environment const & env, scoped_ext const & ext) {
        return env.update(g_ext->m_ext_id, std::make_shared<scoped_ext>(ext));
    }
    static environment using_namespace_fn(environment const & env, io_state const & ios, name const & n) {
        return update(env, get(env).using_namespace(env, ios, n));
    }
    static environment export_namespace_fn(environment const & env, io_state const & ios, name const & n) {
        return get(env).export_namespace(env, ios, n);
    }
    static environment push_fn(environment const & env, io_state const &, scope_kind) {
        return update(env, get(env).push());
    }
    static environment pop_fn(environment const & env, io_state const & ios, scope_kind k) {
        auto p = get(env).pop(k);
        environment new_env = update(env, p.first);
        buffer<entry> entries;
        to_buffer(p.second, entries);
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            new_env = update(new_env, get(new_env)._add_tmp_entry(new_env, ios, entries[i]));
        }
        return new_env;
    }

    static environment register_entry(environment const & env, io_state const & ios, name const & n, entry const & e) {
        return update(env, get(env)._register_entry(env, ios, n, e));
    }

    static environment add_entry(environment env, io_state const & ios, entry const & e, name const & n, bool persistent) {
        if (auto h = get_fingerprint(e)) {
            env = update_fingerprint(env, *h);
        }
        if (n == get_namespace(env)) {
            if (!persistent) {
                return update(env, get(env)._add_tmp_entry(env, ios, e));
            } else {
                name n = get_namespace(env);
                env = module::add(env, get_serialization_key(), [=](environment const &, serializer & s) {
                        s << n;
                        write_entry(s, e);
                    });
                return update(env, get(env)._add_entry(env, ios, e));
            }
        } else {
            lean_assert(persistent);
            // add entry in a namespace that is not the current one
            env = module::add(env, get_serialization_key(), [=](environment const &, serializer & s) {
                    s << n;
                    write_entry(s, e);
                });
            env = add_namespace(env, n);
            return update(env, get(env)._add_entry_at(env, ios, e, n));
        }
    }

    static void reader(deserializer & d, shared_environment &,
                       std::function<void(asynch_update_fn const &)> &,
                       std::function<void(delayed_update_fn const &)> & add_delayed_update) {
        name n;
        d >> n;
        entry e = read_entry(d);
        add_delayed_update([=](environment const & env, io_state const & ios) -> environment {
                return register_entry(env, ios, n, e);
            });
    }
    static state const & get_state(environment const & env) {
        return get(env).m_state;
    }
    /** \brief Return the entries/attributes associated with the given namespace */
    static list<entry> const * get_entries(environment const & env, name const & n) {
        return get(env).m_entries_map.find(n);
    }
};

template<typename Config>
typename scoped_ext<Config>::reg * scoped_ext<Config>::g_ext = nullptr;

void initialize_scoped_ext();
void finalize_scoped_ext();
}
