/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include "util/list.h"
#include "util/rb_map.h"
#include "util/name.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/module.h"
#include "library/fingerprint.h"

namespace lean {
enum class scope_kind { Namespace, Section };
enum class persistence { scope, file, global };

typedef environment (*push_scope_fn)(environment const &, io_state const &, scope_kind);
typedef environment (*pop_scope_fn)(environment const &, io_state const &, scope_kind);

void register_scoped_ext(push_scope_fn push, pop_scope_fn pop);

/** \brief Create a new scope, all scoped extensions are notified. */
environment push_scope(environment const & env, io_state const & ios, scope_kind k, name const & n = name());
/** \brief Delete the most recent scope, all scoped extensions are notified.
    \remark method throws an exception if there are no open scopes, or \c n does not match the name of the open scope
*/
environment pop_scope(environment const & env, io_state const & ios, name const & n = name());
/** \brief Similar to \c pop_scope, but it always succeed.
    It always pops the current open scope, and does nothing if there are no open scopes.
*/
environment pop_scope_core(environment const & env, io_state const & ios);
/** \brief Return true iff there are open scopes */
bool has_open_scopes(environment const & env);

/** \brief Add a new namespace (if it does not exist) */
environment add_namespace(environment const & env, name const & ns);

name const & get_namespace(environment const & env);
name const & get_scope_header(environment const & env);
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

std::vector<name> get_namespace_completion_candidates(environment const & env);

/** \brief Mark the given namespace as opened */
environment mark_namespace_as_open(environment const & env, name const & n);
/** \brief Return the set of namespaces marked as "open" using \c mark_namespace_as_open. */
name_set get_opened_namespaces(environment const & env);

/** \brief Return true iff \c n is a namespace */
bool is_namespace(environment const & env, name const & n);

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
    static const char * get_serialization_key() { return Config::get_serialization_key(); }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return Config::get_fingerprint(e);
    }

    /* Stack of states, it is updated using push/pop operations */
    list<state>           m_scopes;
    state                 m_state; // explicit top-most (current) scope

    /* Add \c e to all states in \c l. */
    static list<state> add_all(environment const & env, io_state const & ios, list<state> const & l, entry const & e) {
        if (is_nil(l)) {
            return l;
        } else {
            state new_s = head(l);
            add_entry(env, ios, new_s, e);
            return cons(new_s, add_all(env, ios, tail(l), e));
        }
    }

    /* Add persistent entry, updating all states with this entry. This method is invoked when importing files. */
    scoped_ext _register_entry(environment const & env, io_state const & ios, entry const & e) const {
        scoped_ext r(*this);
        add_entry(env, ios, r.m_state, e);
        r.m_scopes = add_all(env, ios, r.m_scopes, e);
        return r;
    }

    /* Add entry to current state */
    scoped_ext _add_tmp_entry(environment const & env, io_state const & ios, entry const & e) const {
        scoped_ext r(*this);
        add_entry(env, ios, r.m_state, e);
        return r;
    }

public:
    /** \brief Open a namespace/section. It returns the new updated state. */
    scoped_ext push() const {
        scoped_ext r(*this);
        r.m_scopes           = cons(m_state, r.m_scopes);
        return r;
    }

    /** \brief Close namespace/section. It returns the new updated state.
        \pre There are open namespaces */
    scoped_ext pop() const {
        lean_assert(!is_nil(m_scopes));
        scoped_ext r(*this);
        r.m_state  = head(m_scopes);
        r.m_scopes = tail(m_scopes);
        return r;
    }

    struct modification : public lean::modification {
        LEAN_MODIFICATION(get_serialization_key())

        entry m_entry;

        modification() {}
        modification(entry const & e) : m_entry(e) {}

        void perform(environment & env) const override {
            env = register_entry(env, get_global_ios(), m_entry);
        }

        void serialize(serializer & s) const override {
            write_entry(s, m_entry);
        }

        static std::shared_ptr<lean::modification const> deserialize(deserializer & d) {
            return std::make_shared<modification>(read_entry(d));
        }
    };

    struct reg {
        unsigned m_ext_id;
        reg() {
            register_scoped_ext(push_fn, pop_fn);
            modification::init();
            m_ext_id = environment::register_extension(std::make_shared<scoped_ext>());
        }
        ~reg() {
            modification::finalize();
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
    static environment push_fn(environment const & env, io_state const &, scope_kind) {
        return update(env, get(env).push());
    }
    static environment pop_fn(environment const & env, io_state const &, scope_kind) {
        return update(env, get(env).pop());
    }

    static environment register_entry(environment const & env, io_state const & ios, entry const & e) {
        return update(env, get(env)._register_entry(env, ios, e));
    }

    static environment add_entry(environment env, io_state const & ios, entry const & e, persistence persist) {
        if (auto h = get_fingerprint(e)) {
            env = update_fingerprint(env, *h);
        }
        if (persist == persistence::scope) {
            return update(env, get(env)._add_tmp_entry(env, ios, e));
        } else {
            if (persist == persistence::global) {
                env = module::add(env, std::make_shared<modification>(e));
            }
            return update(env, get(env)._register_entry(env, ios, e));
        }
    }

    static environment add_entry(environment const & env, io_state const & ios, entry const & e, bool persistent) {
        return add_entry(env, ios, e, persistent ? persistence::global : persistence::scope);
    }

    static state const & get_state(environment const & env) {
        return get(env).m_state;
    }
};

template<typename Config>
typename scoped_ext<Config>::reg * scoped_ext<Config>::g_ext = nullptr;


void initialize_scoped_ext();
void finalize_scoped_ext();
}
