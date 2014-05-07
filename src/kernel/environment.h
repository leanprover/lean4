/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <memory>
#include <vector>
#include "util/rc.h"
#include "util/optional.h"
#include "util/list.h"
#include "util/rb_map.h"
#include "util/name_set.h"
#include "kernel/expr.h"
#include "kernel/constraint.h"
#include "kernel/definition.h"

namespace lean {
class type_checker;
class environment;
class certified_definition;

/**
   \brief The Lean kernel can be instantiated with different normalization extensions.
   Each extension is part of the trusted code base. The extensions allow us to support
   different flavors of the core type theory. We will use these extensions to implement
   inductive datatype (ala Coq), HIT, record types, etc.
*/
class normalizer_extension {
public:
    virtual ~normalizer_extension() {}
    virtual optional<expr> operator()(expr const & e, extension_context & ctx) const = 0;
};

/**
   \brief The header of an environment is created when we create the empty environment.
   Moreover if environment B is an extension of environment A, then A and B share the same header.
*/
class environment_header {
    /* In the following field, 0 means untrusted mode (i.e., check everything),
       >= 1 means do not check imported modules, and do not check macros
       with level less than the value of this field.
    */
    unsigned m_trust_lvl; //!the given one.
    bool m_proof_irrel;   //!< true if the kernel assumes proof irrelevance
    bool m_eta;           //!< true if the kernel uses eta-reduction in convertability checks
    bool m_impredicative; //!< true if the kernel should treat (universe level 0) as a impredicative Prop/Bool.
    std::unique_ptr<normalizer_extension const> m_norm_ext;
    void dealloc();
public:
    environment_header(unsigned trust_lvl, bool proof_irrel, bool eta, bool impredicative, std::unique_ptr<normalizer_extension const> ext);
    unsigned trust_lvl() const { return m_trust_lvl; }
    bool proof_irrel() const { return m_proof_irrel; }
    bool eta() const { return m_eta; }
    bool impredicative() const { return m_impredicative; }
    normalizer_extension const & norm_ext() const { return *(m_norm_ext.get()); }
};

class environment_extension {
public:
    virtual ~environment_extension();
};

typedef std::vector<std::shared_ptr<environment_extension const>> environment_extensions;

/**
   \brief environment identifier that allows us to track descendants of a given environment.
*/
class environment_id {
    friend class environment; // Only the environment class can create object of this type.
    list<unsigned> m_trail; //!< trail of ancestors. The unsigned value is redundant, it store the depth of the trail.
    /**
        \brief Create an identifier for an environment that is a direct descendant of the given one.
        The bool field is just to make sure this constructor is not confused with a copy constructor
    */
    environment_id(environment_id const & ancestor, bool);
    /** \brief Create an identifier for an environment without ancestors (e.g., empty environment) */
    environment_id();
    /** Create an identifier for an environment that is a direct descendant of the given one. */
    static environment_id mk_descendant(environment_id const & ancestor) { return environment_id(ancestor, true); }
public:
    /** \brief Return true iff this object is a descendant of the given one. */
    bool is_descendant(environment_id const & id) const;
};

/**
   \brief Lean core environment. An environment object can be extended/customized in different ways:

   1- By providing a normalizer_extension when creating an empty environment.
   2- By setting the proof_irrel and eta flags when creating an empty environment.
   3- By attaching additional data as environment::extensions. The additional data can be added
      at any time. They contain information used by the automation (e.g., rewriting sets, unification hints, etc).
*/
class environment {
    typedef std::shared_ptr<environment_header const>     header;
    typedef rb_map<name, definition, name_quick_cmp>      definitions;
    typedef std::shared_ptr<environment_extensions const> extensions;

    header         m_header;
    environment_id m_id;
    definitions    m_definitions;
    name_set       m_global_levels;
    extensions     m_extensions;

    environment(header const & h, environment_id const & id, definitions const & d, name_set const & global_levels, extensions const & ext);

public:
    environment(unsigned trust_lvl = 0, bool proof_irrel = true, bool eta = true, bool impredicative = true);
    environment(unsigned trust_lvl, bool proof_irrel, bool eta, bool impredicative, std::unique_ptr<normalizer_extension> ext);
    ~environment();

    /** \brief Return the environment unique identifier. */
    environment_id const & get_id() const { return m_id; }

    /** \brief Return true iff this environment is a descendant of \c env. */
    bool is_descendant(environment const & env) const { return m_id.is_descendant(env.m_id); }

    /** \brief Return the trust level of this environment. */
    unsigned trust_lvl() const { return m_header->trust_lvl(); }

    /** \brief Return true iff the environment assumes proof irrelevance */
    bool proof_irrel() const { return m_header->proof_irrel(); }

    /** \brief Return true iff the environment assumes Eta-reduction */
    bool eta() const { return m_header->eta(); }

    /** \brief Return true iff the environment treats universe level 0 as an impredicative Prop/Bool */
    bool impredicative() const { return m_header->impredicative(); }

    /** \brief Return reference to the normalizer extension associatied with this environment. */
    normalizer_extension const & norm_ext() const { return m_header->norm_ext(); }

    /** \brief Return definition with name \c n (if it is defined in this environment). */
    optional<definition> find(name const & n) const;

    /** \brief Return definition with name \c n. Throws and exception if definition does not exist in this environment. */
    definition get(name const & n) const;

    /**
        \brief Add a new global universe level with name \c n
        This method throws an exception if the environment already contains a level named \c n.
    */
    environment add_global_level(name const & n) const;

    /** \brief Return true iff the environment has a universe level named \c n. */
    bool is_global_level(name const & n) const;

    /**
       \brief Extends the current environment with the given (certified) definition
       This method throws an exception if:
          - The definition was certified in an environment which is not an ancestor of this one.
          - The environment already contains a definition with the given name.
    */
    environment add(certified_definition const & d) const;

    /**
       \brief Replace the axiom with name <tt>t.get_definition().get_name()</tt> with the theorem t.get_definition().
       This method throws an exception if:
          - The theorem was certified in an environment which is not an ancestor of this one.
          - The environment does not contain an axiom named <tt>t.get_definition().get_name()</tt>
    */
    environment replace(certified_definition const & t) const;

    /**
       \brief Register an environment extension. Every environment
       object may contain this extension. The argument \c initial is
       the initial value for the new extensions. The extension object
       can be retrieved using the given token (unsigned integer) returned
       by this method.

       \remark The extension objects are created on demand.

       \see get_extension
    */
    static unsigned register_extension(std::shared_ptr<environment_extension const> const & initial);

    /** \brief Return the extension with the given id. */
    environment_extension const & get_extension(unsigned extid) const;

    /** \brief Update the environment extension with the given id. */
    environment update(unsigned extid, std::shared_ptr<environment_extension const> const & ext) const;
};

class name_generator;

/**
   \brief A certified definition is one that has been type checked.
   Only the type_checker class can create certified definitions.
*/
class certified_definition {
    friend certified_definition check(environment const & env, name_generator const & g, definition const & d, bool memoize, name_set const & extra_opaque);
    environment_id m_id;
    definition     m_definition;
    certified_definition(environment_id const & id, definition const & d):m_id(id), m_definition(d) {}
public:
    /** \brief Return the id of the environment that was used to type check this definition. */
    environment_id const & get_id() const { return m_id; }
    definition const & get_definition() const { return m_definition; }
};
}
