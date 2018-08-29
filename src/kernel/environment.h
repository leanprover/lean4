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

/** \brief Lean core environment. An environment object can be extended/customized in different ways:

    1- By providing a normalizer_extension when creating an empty environment.
    2- By attaching additional data as environment::extensions. The additional data can be added
       at any time. They contain information used by the automation (e.g., rewriting sets, unification hints, etc). */
class environment {
    typedef std::shared_ptr<environment_header const>     header;
    typedef name_map<constant_info>                       constants;
    typedef std::shared_ptr<environment_extensions const> extensions;
    friend class add_inductive_fn;

    header                    m_header;
    bool                      m_quot_initialized{false};
    constants                 m_constants;
    extensions                m_extensions;

    environment(environment const & env, extensions const & exts):
        m_header(env.m_header), m_quot_initialized(env.m_quot_initialized), m_constants(env.m_constants), m_extensions(exts) {}

    void check_duplicated_univ_params(level_param_names ls) const;
    void check_name(name const & n) const;

    void add_core(constant_info const & info) { m_constants.insert(info.get_name(), info); }
    environment add(constant_info const & info) const {
        environment new_env(*this);
        new_env.add_core(info);
        return new_env;
    }
    environment add_axiom(declaration const & d, bool check) const;
    environment add_definition(declaration const & d, bool check) const;
    environment add_theorem(declaration const & d, bool check) const;
    environment add_mutual(declaration const & d, bool check) const;
    environment add_quot() const;
    environment add_inductive(declaration const & d) const;

public:
    environment(unsigned trust_lvl = 0);
    environment(unsigned trust_lvl, std::unique_ptr<normalizer_extension> ext);
    ~environment();

    /** \brief Return the trust level of this environment. */
    unsigned trust_lvl() const { return m_header->trust_lvl(); }

    bool is_recursor(name const & n) const;

    bool is_builtin(name const & n) const;

    bool is_quot_initialized() const { return m_quot_initialized; }

    /** \brief Return reference to the normalizer extension associatied with this environment. */
    normalizer_extension const & norm_ext() const { return m_header->norm_ext(); }

    /** \brief Return information for the constant with name \c n (if it is defined in this environment). */
    optional<constant_info> find(name const & n) const;

    /** \brief Return information for the constant with name \c n. Throws and exception if constant declaration does not exist in this environment. */
    constant_info get(name const & n) const;

    /** \brief Extends the current environment with the given declaration */
    environment add(declaration const & d, bool check = true) const;

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

    /** \brief Apply the function \c f to each constant */
    void for_each_constant(std::function<void(constant_info const & d)> const & f) const;

    /** \brief Return true iff declarations and extensions of e1 and e2 are pointer equal */
    friend bool is_eqp(environment const & e1, environment const & e2) {
        return
            is_eqp(e1.m_constants, e2.m_constants) &&
            e1.m_extensions.get() == e2.m_extensions.get();
    }

    friend bool is_decl_eqp(environment const & e1, environment const & e2) {
        return is_eqp(e1.m_constants, e2.m_constants);
    }
};

void check_no_metavar_no_fvar(environment const & env, name const & n, expr const & e);

void initialize_environment();
void finalize_environment();
}
