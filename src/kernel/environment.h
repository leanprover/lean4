/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <memory>
#include <vector>
#include "runtime/optional.h"
#include "util/rc.h"
#include "util/list.h"
#include "util/rb_map.h"
#include "util/name_set.h"
#include "util/name_map.h"
#include "kernel/expr.h"
#include "kernel/declaration.h"
#include "kernel/normalizer_extension.h"

#ifndef LEAN_BELIEVER_TRUST_LEVEL
/* If an environment E is created with a trust level > LEAN_BELIEVER_TRUST_LEVEL, then
   we can add declarations to E without type checking them. */
#define LEAN_BELIEVER_TRUST_LEVEL 1024
#endif

namespace lean {
class old_type_checker;
class environment;
class certified_declaration;
namespace inductive { class certified_inductive_decl; }

typedef std::function<bool(name const &)> extra_opaque_pred; // NOLINT
extra_opaque_pred const & no_extra_opaque();

/** \brief The header of an environment is created when we create the empty environment.
    Moreover if environment B is an extension of environment A, then A and B share the same header. */
class environment_header {
    /* In the following field, 0 means untrusted mode (i.e., check everything),
       higher level allow us to trust the implementation of macros, and even
       allow us to add declarations without type checking them (e.g., m_trust_lvl > LEAN_BELIEVER_TRUST_LEVEL) */
    unsigned m_trust_lvl;
    std::unique_ptr<normalizer_extension const> m_norm_ext;
    void dealloc();
public:
    environment_header(unsigned trust_lvl, std::unique_ptr<normalizer_extension const> ext);
    unsigned trust_lvl() const { return m_trust_lvl; }
    normalizer_extension const & norm_ext() const { return *(m_norm_ext.get()); }
    bool is_recursor(environment const & env, name const & n) const { return m_norm_ext->is_recursor(env, n); }
    bool is_builtin(environment const & env, name const & n) const { return m_norm_ext->is_builtin(env, n); }
};

class environment_extension {
public:
    virtual ~environment_extension();
};

typedef std::vector<std::shared_ptr<environment_extension const>> environment_extensions;

/** \brief environment identifier for tracking descendants of a given environment.

    It is used in the following places:
    1) `environment::add`: to check whether the certified declaration has been type checked
       in an "ancestor" of the `this` environment.

    2) `environment::replace`: (similar to previous case) to check whether the new declaration
       has been type checked in an "ancestor" of the `this` environment.

    3) `tactic.set_env`: to check whether the new environment is a descendant of the environment
       in the current `tactic_state` object.

    4) `vm::update_env`: similar to case 3.

    5) To check whether user_attribute and simp_lemmas thread local caches needs to be reset or not.

    Cases 1 and 2 are needed for soundness. Cases 3 and 4 are necessary to enforce invariants that
    we assume in the frontend, otherwise user defined tactics may break the system. Case 5 can
    be avoided after we stop using thread local caches. */
class environment_id {
    friend class environment_id_tester;
    friend class environment; // Only the environment class can create object of this type.
    struct path;
    path *   m_ptr;
    unsigned m_depth;
    /** \brief Create an identifier for an environment that is a direct descendant of the given one.
        The bool field is just to make sure this constructor is not confused with a copy constructor */
    environment_id(environment_id const & ancestor, bool);
    /** \brief Create an identifier for an environment without ancestors (e.g., empty environment) */
    environment_id();
    /** Create an identifier for an environment that is a direct descendant of the given one. */
    static environment_id mk_descendant(environment_id const & ancestor) { return environment_id(ancestor, true); }
public:
    environment_id(environment_id const & id);
    environment_id(environment_id && id);
    ~environment_id();
    environment_id & operator=(environment_id const & s);
    environment_id & operator=(environment_id && s);

    /** \brief Return true iff this object is a descendant of the given one. */
    bool is_descendant(environment_id const & id) const;
};

/** \brief Lean core environment. An environment object can be extended/customized in different ways:

    1- By providing a normalizer_extension when creating an empty environment.
    2- By attaching additional data as environment::extensions. The additional data can be added
       at any time. They contain information used by the automation (e.g., rewriting sets, unification hints, etc). */
class environment {
    typedef std::shared_ptr<environment_header const>     header;
    typedef name_map<declaration>                         declarations;
    typedef std::shared_ptr<environment_extensions const> extensions;
    friend class add_inductive_fn;

    header                    m_header;
    environment_id            m_id;
    bool                      m_quot_initialized{false};
    declarations              m_declarations;
    extensions                m_extensions;

    environment(environment const & env, declarations const & ds):
        m_header(env.m_header), m_id(environment_id::mk_descendant(env.m_id)), m_quot_initialized(env.m_quot_initialized), m_declarations(ds), m_extensions(env.m_extensions) {}
    environment(environment const & env, extensions const & exts):
        m_header(env.m_header), m_id(environment_id::mk_descendant(env.m_id)), m_quot_initialized(env.m_quot_initialized), m_declarations(env.m_declarations), m_extensions(exts) {}
public:
    environment(unsigned trust_lvl = 0);
    environment(unsigned trust_lvl, std::unique_ptr<normalizer_extension> ext);
    ~environment();

    /** \brief Return the environment unique identifier. */
    environment_id const & get_id() const { return m_id; }

    /** \brief Return true iff this environment is a descendant of \c env. */
    bool is_descendant(environment const & env) const { return m_id.is_descendant(env.m_id); }

    /** \brief Return the trust level of this environment. */
    unsigned trust_lvl() const { return m_header->trust_lvl(); }

    bool is_recursor(name const & n) const;

    bool is_builtin(name const & n) const;

    bool is_quot_initialized() const { return m_quot_initialized; }

    /** \brief Return reference to the normalizer extension associatied with this environment. */
    normalizer_extension const & norm_ext() const { return m_header->norm_ext(); }

    /** \brief Return declaration with name \c n (if it is defined in this environment). */
    optional<declaration> find(name const & n) const;

    /** \brief Return declaration with name \c n. Throws and exception if declaration does not exist in this environment. */
    declaration get(name const & n) const;

    /** \brief Extends the current environment with the given (certified) declaration
        This method throws an exception if:
          - The declaration was certified in an environment which is not an ancestor of this one.
          - The environment already contains a declaration with the given name. */
    environment add(certified_declaration const & d) const;

    /** \brief Replace the axiom with name <tt>t.get_declaration().get_name()</tt> with the theorem t.get_declaration().
        This method throws an exception if:
          - The theorem was certified in an environment which is not an ancestor of this one.
          - The environment does not contain an axiom named <tt>t.get_declaration().get_name()</tt> */
    environment replace(certified_declaration const & t) const;

    /** \brief Add a sequence of (possibly mutually recursive) meta declarations.
        The type checking occurs in two phases:
        1- We type check each declaration type and add to a new environment.
        2- We type check the definitions body.

        If \c check is false, then type checking is skipped. */
    environment add_meta(buffer<declaration> const & ds, bool check = true) const;

    /* \brief Add `quot` type. */
    environment add_quot() const;

    /* \brief Add (mutually recursive) inductive declarations */
    environment add(inductive_decl const & decl) const;

    /** \brief Register an environment extension. Every environment
        object may contain this extension. The argument \c initial is
        the initial value for the new extensions. The extension object
        can be retrieved using the given token (unsigned integer) returned
        by this method.

        \remark The extension objects are created on demand.

        \see get_extension */
    static unsigned register_extension(std::shared_ptr<environment_extension const> const & initial);

    /** \brief Return the extension with the given id. */
    environment_extension const & get_extension(unsigned extid) const;

    /** \brief Update the environment extension with the given id. */
    environment update(unsigned extid, std::shared_ptr<environment_extension const> const & ext) const;

    /** \brief Return a new environment, where its "history" has been truncated/forgotten.
        That is, <tt>is_descendant(e)</tt> will return false for any environment \c e that
        is not pointer equal to the result. */
    environment forget() const;

    /** \brief Apply the function \c f to each declaration */
    void for_each_declaration(std::function<void(declaration const & d)> const & f) const;

    /** \brief Return true iff declarations and extensions of e1 and e2 are pointer equal */
    friend bool is_eqp(environment const & e1, environment const & e2) {
        return
            is_eqp(e1.m_declarations, e2.m_declarations) &&
            e1.m_extensions.get() == e2.m_extensions.get();
    }

    friend bool is_decl_eqp(environment const & e1, environment const & e2) {
        return is_eqp(e1.m_declarations, e2.m_declarations);
    }
};

void initialize_environment();
void finalize_environment();

class name_generator;

/** \brief A certified declaration is one that has been type checked.
    Only the type_checker class can create certified declarations. */
class certified_declaration {
    friend class certify_unchecked;
    friend certified_declaration check(environment const & env, declaration const & d);
    environment_id m_id;
    declaration    m_declaration;
    certified_declaration(environment_id const & id, declaration const & d):m_id(id), m_declaration(d) {}
public:
    /** \brief Return the id of the environment that was used to type check this declaration. */
    environment_id const & get_id() const { return m_id; }
    declaration const & get_declaration() const { return m_declaration; }
    /** \brief Certifies a declaration without type-checking.

       \remark This method throws an excetion if trust_lvl() == 0
       It is only used when importing pre-compiled .olean files and for inductive definitions, and trust_lvl() > 0. */
    static certified_declaration certify(environment const & env, declaration const & d);
    static certified_declaration certify_or_check(environment const & env, declaration const & d);
};
}
